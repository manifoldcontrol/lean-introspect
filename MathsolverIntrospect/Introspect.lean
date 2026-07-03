/-
Mathsolver / Introspect

Proof-term transport: elaborate a candidate theorem, walk its proof term as a DAG,
emit JSON to stdout delimited by markers so the Python side can extract it from
the lean-runner output stream.

Usage in a candidate file:

  import MathsolverIntrospect.Introspect

  theorem candidate_thm (n : Nat) : n + 0 = n := by simp

  #introspect candidate_thm

A typical consumer wraps a candidate file, runs
`lake env lean <file>` in the MathsolverIntrospect project, captures stdout, and
extracts the JSON between the `---PROOFTERM-DAG-BEGIN---` / `---END---` markers.

The output has two parts: proof-term content (nodes, edges, labels) and a
leakage report (unresolved metavariables, sorry usage, status). Structural
metrics consume the former; audit/retention logic consumes the latter.
-/

import Lean

namespace MathsolverIntrospect.Introspect

open Lean Elab Command

/-- A node in the proof-term DAG. `kind` is the Expr constructor name;
    `label` is a short human-readable description. -/
structure DAGNode where
  id : String
  kind : String
  label : String
deriving Lean.ToJson

/-- A parent-child edge between two DAG nodes. -/
structure DAGEdge where
  source : String
  target : String
deriving Lean.ToJson

/-- The transport output. Compatible with the Python `proof_term_dag.py` reader. -/
structure ProofTermDAG where
  candidate_name : String
  /-- "closed" - no metavariables, no sorry; the kernel accepted a complete term.
      "open"   - at least one unresolved metavariable or sorry was found.
      "missing" - the constant was not in the environment. -/
  status : String
  uses_sorry : Bool
  nodes : Array DAGNode
  edges : Array DAGEdge
  dependency_surface : Array String
  unresolved_mvars : Array String
deriving Lean.ToJson

/-- Internal state for the DAG walker. -/
structure WalkState where
  counter : Nat := 0
  nodes : Array DAGNode := #[]
  edges : Array DAGEdge := #[]
  deps : Lean.NameSet := {}
  mvars : Array String := #[]
  usesSorry : Bool := false

abbrev BuildM := StateM WalkState

/-- Recursively walk a `Lean.Expr`, emitting one node per subterm and edges
    from parent to child. The walker is pure (StateM) - no kernel calls, no
    metavariable instantiation; it inspects the Expr structure as-is. -/
partial def walkExpr (e : Expr) : BuildM String := do
  let s ← get
  let id := s!"n{s.counter}"
  modify fun s => { s with counter := s.counter + 1 }
  match e with
  | .const n _ =>
    modify fun s =>
      { s with
        nodes := s.nodes.push { id, kind := "const", label := toString n }
        deps := s.deps.insert n
        usesSorry := s.usesSorry || n == ``sorryAx }
    return id
  | .app f a =>
    modify fun s =>
      { s with nodes := s.nodes.push { id, kind := "app", label := "app" } }
    let fid ← walkExpr f
    let aid ← walkExpr a
    modify fun s =>
      { s with edges :=
          (s.edges.push { source := id, target := fid }).push
                       { source := id, target := aid } }
    return id
  | .lam n _ body _ =>
    modify fun s =>
      { s with nodes := s.nodes.push { id, kind := "lam", label := s!"λ {n}" } }
    let bid ← walkExpr body
    modify fun s =>
      { s with edges := s.edges.push { source := id, target := bid } }
    return id
  | .forallE n _ body _ =>
    modify fun s =>
      { s with nodes := s.nodes.push { id, kind := "forall", label := s!"∀ {n}" } }
    let bid ← walkExpr body
    modify fun s =>
      { s with edges := s.edges.push { source := id, target := bid } }
    return id
  | .letE n _ value body _ =>
    modify fun s =>
      { s with nodes := s.nodes.push { id, kind := "let", label := s!"let {n}" } }
    let vid ← walkExpr value
    let bid ← walkExpr body
    modify fun s =>
      { s with edges :=
          (s.edges.push { source := id, target := vid }).push
                       { source := id, target := bid } }
    return id
  | .mvar mvarId =>
    let label := s!"?{mvarId.name}"
    modify fun s =>
      { s with
        nodes := s.nodes.push { id, kind := "mvar", label }
        mvars := s.mvars.push label }
    return id
  | .fvar fvarId =>
    modify fun s =>
      { s with nodes := s.nodes.push
                          { id, kind := "fvar", label := toString fvarId.name } }
    return id
  | .bvar i =>
    modify fun s =>
      { s with nodes := s.nodes.push { id, kind := "bvar", label := s!"#{i}" } }
    return id
  | .lit l =>
    let label := match l with
      | .natVal n => toString n
      | .strVal s => s!"\"{s}\""
    modify fun s =>
      { s with nodes := s.nodes.push { id, kind := "lit", label } }
    return id
  | .sort _ =>
    modify fun s =>
      { s with nodes := s.nodes.push { id, kind := "sort", label := "Sort" } }
    return id
  | .mdata _ inner =>
    modify fun s =>
      { s with nodes := s.nodes.push { id, kind := "mdata", label := "mdata" } }
    let iid ← walkExpr inner
    modify fun s =>
      { s with edges := s.edges.push { source := id, target := iid } }
    return id
  | .proj typeName idx struct =>
    modify fun s =>
      { s with
        nodes := s.nodes.push
                   { id, kind := "proj", label := s!".{typeName}.{idx}" }
        deps := s.deps.insert typeName }
    let sid ← walkExpr struct
    modify fun s =>
      { s with edges := s.edges.push { source := id, target := sid } }
    return id

/-- Build a DAG from a `ConstantInfo`. Only theorems and definitions have a
    proof-term value; other ConstantInfo kinds yield a "missing" status. -/
def buildDAG (info : ConstantInfo) : ProofTermDAG :=
  let candidateName := toString info.name
  let value? : Option Expr := match info with
    | .thmInfo t => some t.value
    | .defnInfo d => some d.value
    | _ => none
  match value? with
  | none =>
    { candidate_name := candidateName
      status := "missing"
      uses_sorry := false
      nodes := #[]
      edges := #[]
      dependency_surface := #[]
      unresolved_mvars := #[] }
  | some value =>
    let (_, finalState) := (walkExpr value).run {}
    let status :=
      if !finalState.mvars.isEmpty || finalState.usesSorry then "open" else "closed"
    { candidate_name := candidateName
      status
      uses_sorry := finalState.usesSorry
      nodes := finalState.nodes
      edges := finalState.edges
      dependency_surface := finalState.deps.toArray.map toString
      unresolved_mvars := finalState.mvars }

/-- The `#introspect <name>` command. Looks up `<name>` in the current
    environment, walks its proof term, and emits the DAG as JSON to stdout
    bracketed by `---PROOFTERM-DAG-BEGIN---` / `---PROOFTERM-DAG-END---`. -/
syntax (name := introspectCmd) "#introspect " ident : command

@[command_elab introspectCmd]
def elabIntrospect : CommandElab := fun stx => do
  match stx with
  | `(#introspect $id:ident) =>
    let env ← getEnv
    let name := id.getId
    let dag : ProofTermDAG :=
      match env.find? name with
      | none =>
        { candidate_name := toString name
          status := "missing"
          uses_sorry := false
          nodes := #[]
          edges := #[]
          dependency_surface := #[]
          unresolved_mvars := #[] }
      | some info => buildDAG info
    let json := (Lean.toJson dag).pretty
    IO.println "---PROOFTERM-DAG-BEGIN---"
    IO.println json
    IO.println "---PROOFTERM-DAG-END---"
  | _ => throwError "expected: #introspect <ident>"

end MathsolverIntrospect.Introspect
