/-
  OP-00008: Pillai's conjecture on axⁿ − byᵐ = c

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00008

      theorem resolution : RegistryProblems.Problem_OP_00008 := ...

  Formalised by The Formal Conjectures Authors, not by clopen.solutions:
  https://github.com/google-deepmind/formal-conjectures/blob/0771383387505c96d1b2f6a3d35088ad00892c5c/FormalConjectures/Wikipedia/Catalan.lean#L42

  Copyright 2025 The Formal Conjectures Authors.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The statement is the source theorem's proposition as
  Lean prints it, checked to elaborate to the same term. The source's name,
  attributes, docstring and proof are not carried over.
-/

import Mathlib

namespace RegistryProblems

/-- OP-00008: Pillai's conjecture on axⁿ − byᵐ = c -/
def Problem_OP_00008 : Prop :=
  ∀ (a b c : ℕ),
      0 < a →
        0 < b →
          0 < c →
            {(x, y, m, n) |
                1 < x ∧ 1 < y ∧ 1 < m ∧ 1 < n ∧ (m, n) ≠ (2, 2) ∧ a * x ^ n - b * y ^ m = c}.Finite

end RegistryProblems
