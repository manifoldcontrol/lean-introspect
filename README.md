# lean-introspect

a lean 4 `#introspect` command: elaborate a theorem, walk its proof term as a dag, and emit json. proof-term structure plus a leakage report (`sorry` usage, unresolved metavariables, open/closed status).

built for proof pipelines that need to audit what the kernel accepted, not just whether it accepted: verifier-bounded proof search, proof-term metrics, statement-adequacy checking, provenance systems.

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
  "unresolved_mvars": []
}
```

- `status: "closed"`: no metavariables, no `sorry`; the kernel accepted a complete term. `"open"`: at least one mvar or `sorryAx` in the term. `"missing"`: the name is not in the environment, or is not a theorem/def.
- `nodes`/`edges`: one node per `Expr` subterm (const/app/lam/forall/let/...), edges parent to child, matching the elaborated term's structure.
- `dependency_surface`: every constant the proof term references, axioms included (check for `Classical.choice`, `sorryAx`, ...).

the markers make extraction simple from a runner's stdout stream; parse the first block per run.

## setup

requires elan. the project pins `leanprover/lean4:v4.30.0` with mathlib pinned to the matching release (see `lakefile.toml`).

```
lake exe cache get   # fetch mathlib oleans, once
lake build
lake env lean test_introspect.lean   # smoke test
```

## limitations (v0.1)

- named declarations only. `#introspect` takes an identifier; anonymous `example`s can't be addressed. wrap them in a named `theorem`.
- theorems and defs only. other `ConstantInfo` kinds report `"missing"`.
- no elaborated-type emit yet. the leakage report does not include the elaborated statement type (needed to detect when `autoImplicit` silently generalized an intended constant). top roadmap item.
- the walker inspects the stored `Expr` as-is: no kernel calls, no mvar instantiation.

## why a leakage report

a kernel accept is not the end of the audit. a proof can be accepted and vacuous (autoImplicit generalization), accepted and incomplete (`sorry` elaborates with a warning and exit code 0), accepted and classical where you expected constructive (check `dependency_surface`). `#introspect` exposes the evidence a retention gate needs to refuse those.

## related

[verification-events](https://github.com/manifoldcontrol/verification-events) (provenance event schema) and [csr-seed](https://github.com/manifoldcontrol/csr-seed) (corpus semantic registry).
