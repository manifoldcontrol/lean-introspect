/-
Manual smoke test for the proof-term transport.

Run from inside the MathsolverIntrospect/ directory:

    lake env lean test_introspect.lean

You should see two JSON blocks delimited by ---PROOFTERM-DAG-BEGIN--- markers:
the first for a closed proof, the second for a proof containing `sorry`.
-/

import MathsolverIntrospect.Introspect

theorem nat_add_zero (n : Nat) : n + 0 = n := by simp

#introspect nat_add_zero

theorem incomplete (n : Nat) : n + 0 = n := by sorry

#introspect incomplete
