# lean-introspect

a lean 4 `#introspect` command: elaborate a theorem, walk its proof term as a dag, and emit json. proof-term structure plus a leakage report (`sorry` usage, unresolved metavariables, open/closed status).

built for proof pipelines that need to audit what the kernel accepted, not just whether it accepted: verifier-bounded proof search, proof-term metrics, statement-adequacy checking, provenance systems.

the walk is memoized on `Expr` identity, so a shared subterm is visited once and the emitted counts are true DAG sizes. this matters on real proofs: reflection-style certificates (`ring`, `field_simp`, `nlinarith`) share subterms deeply, and an unmemoized tree walk is exponential in sharing depth -- a 3-variable `by ring` identity elaborates in ~0.2s and then hangs a naive walk for over 150 seconds.

## usage

```lean
import MathsolverIntrospect.Introspect

theorem my_thm (n : Nat) : n + 0 = n := by simp

#introspect my_thm
```

running the file (`lake env lean MyFile.lean`) prints, between `---PROOFTERM-DAG-BEGIN---` / `---PROOFTERM-DAG-END---` markers on stdout:

```json
{
  "candidate_name": "my_thm",
  "status": "closed",
  "uses_sorry": false,
  "nodes": [ {"id": "n0", "kind": "app", "label": "app"}, ... ],
  "edges": [ {"source": "n0", "target": "n1"}, ... ],
  "dependency_surface": ["Nat", "Eq", "of_eq_true", ...],
  "unresolved_mvars": [],
  "elaborated_type": "\u2200 (n : Nat), n + 0 = n",
  "axioms": [],
  "heartbeats": 1832
}
```

- `status: "closed"`: no metavariables, no `sorry`; the kernel accepted a complete term. `"open"`: at least one mvar or `sorryAx` in the term. `"missing"`: the name is not in the environment, or is not a theorem/def.
- `nodes`/`edges`: one node per `Expr` subterm (const/app/lam/forall/let/...), edges parent to child, matching the elaborated term's structure.
- `dependency_surface`: every constant the proof term *directly* references. a direct scan cannot see an axiom minted behind a same-file helper -- use `axioms` for that.
- `axioms`: the kernel-transitive axiom set, as `#print axioms` reports it (`Lean.collectAxioms`). this is the field a retention gate should read: `[propext, Classical.choice, Quot.sound]` is classical-clean; anything else is an axiom the direct surface can hide. empty array = not checked.
- `elaborated_type`: the type the kernel actually accepted, to compare against the declared one (catches `autoImplicit` generalization).
- `heartbeats`: heartbeats consumed at emit time; a deterministic per-file cost measure.

the markers make extraction simple from a runner's stdout stream; parse the first block per run.

## setup

requires elan. the project pins `leanprover/lean4:v4.30.0` with mathlib pinned to the matching release (see `lakefile.toml`).

```
lake exe cache get   # fetch mathlib oleans, once
lake build
lake env lean test_introspect.lean   # smoke test
```

## limitations

- named declarations only. `#introspect` takes an identifier; anonymous `example`s can't be addressed. wrap them in a named `theorem`.
- theorems and defs only. other `ConstantInfo` kinds report `"missing"`.
- the walker inspects the stored `Expr` as-is: no kernel calls, no mvar instantiation. `axioms` and `elaborated_type` are emitted alongside the walk by querying the environment, not by the walker.
- `axioms` reports what the kernel records for the named constant; it does not attribute an axiom to a particular subterm.

## windows: path length

Mathlib's deepest build artifacts reach ~150 characters beyond the lake
project root. On Windows, a project cloned deeper than ~100 characters
crosses the 260-character MAX_PATH limit during cache decompression and
builds, and the failures masquerade as missing downloads (os error 3).
Clone shallow (for example `C:\lean\`), or move the project and leave a
junction at the old location; the junction must point FROM the long alias
TO the short real directory, since lake canonicalizes the workspace root.

## why a leakage report

a kernel accept does not settle whether the proof is what you meant. a proof can be accepted and vacuous (autoImplicit generalization), accepted and incomplete (`sorry` elaborates with a warning and exit code 0), accepted and classical where you expected constructive, or resting on an axiom you did not intend (check `axioms`). `#introspect` exposes the evidence a retention gate needs to refuse those.

## related

[verification-events](https://github.com/manifoldcontrol/verification-events) (provenance event schema) and [csr-seed](https://github.com/manifoldcontrol/csr-seed) (corpus semantic registry).
