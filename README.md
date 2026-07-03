# lean-introspect

A Lean 4 `#introspect` command: elaborate a theorem, walk its proof term as a
DAG, and emit machine-readable JSON — proof-term structure plus a **leakage
report** (`sorry` usage, unresolved metavariables, open/closed status).

Built for proof pipelines that need to *audit* what the kernel accepted, not
just whether it accepted: verifier-bounded proof search, proof-term metrics,
statement-adequacy checking, provenance systems.

Part of a verification-infrastructure family:
[verification-events](https://github.com/manifoldcontrol/verification-events) (provenance event schema)
and [csr-seed](https://github.com/manifoldcontrol/csr-seed) (corpus semantic registry).

## Usage

```lean
import MathsolverIntrospect.Introspect

theorem my_thm (n : Nat) : n + 0 = n := by simp

#introspect my_thm
```

Running the file (`lake env lean MyFile.lean`) prints, between
`---PROOFTERM-DAG-BEGIN---` / `---PROOFTERM-DAG-END---` markers on stdout:

```json
{
  "candidate_name": "my_thm",
  "status": "closed",            // "closed" | "open" | "missing"
  "uses_sorry": false,
  "nodes": [ {"id": "n0", "kind": "app", "label": "app"}, ... ],
  "edges": [ {"source": "n0", "target": "n1"}, ... ],
  "dependency_surface": ["Nat", "Eq", "of_eq_true", ...],
  "unresolved_mvars": []
}
```

- `status: "closed"` — no metavariables, no `sorry`: the kernel accepted a
  complete term. `"open"` — at least one mvar or `sorryAx` in the term.
  `"missing"` — the name is not in the environment, or is not a theorem/def.
- `nodes`/`edges` — one node per `Expr` subterm (const/app/lam/forall/let/...),
  edges parent -> child, matching the elaborated term's structure.
- `dependency_surface` — every constant the proof term references (axioms
  included: check for `Classical.choice`, `sorryAx`, ...).

The markers make extraction trivial from a runner's stdout stream; parse the
first block per run.

## Setup

Requires elan. The project pins `leanprover/lean4:v4.30.0` with mathlib
pinned to the matching release (see `lakefile.toml`).

```
lake exe cache get   # fetch mathlib oleans (do this once)
lake build
lake env lean test_introspect.lean   # smoke test
```

## Limitations (v0.1)

- **Named declarations only.** `#introspect` takes an identifier; anonymous
  `example`s can't be addressed — wrap them in a named `theorem`.
- **Theorems and defs only.** Other `ConstantInfo` kinds report `"missing"`.
- **No elaborated-type emit yet.** The leakage report does not yet include
  the elaborated statement type (needed for statement-adequacy checking —
  detecting when `autoImplicit` silently generalized an intended constant).
  This is the top roadmap item.
- The walker inspects the stored `Expr` as-is: no kernel calls, no mvar
  instantiation.

## Why a leakage report

A kernel accept is not the end of the audit. A proof can be accepted *and*
vacuous (autoImplicit generalization), *and* incomplete (`sorry` elaborates
with a warning, exit code 0), *and* classical where you expected constructive
(check `dependency_surface` against the axiom set). `#introspect` exposes
exactly the evidence a retention gate needs to refuse those.
