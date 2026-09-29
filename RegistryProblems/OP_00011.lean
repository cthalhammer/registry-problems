/-
  OP-00011: A 3 × 3 magic square of distinct squares

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00011

      theorem resolution : RegistryProblems.Problem_OP_00011 := ...

  Formalised by The Formal Conjectures Authors, not by clopen.solutions:
  https://github.com/google-deepmind/formal-conjectures/blob/0771383387505c96d1b2f6a3d35088ad00892c5c/FormalConjectures/Wikipedia/MagicSquares.lean#L35

  Copyright 2026 The Formal Conjectures Authors.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The source's `answer(sorry) ↔`, a placeholder for
  whether the answer is yes or no, is removed, leaving the proposition it asks
  about. That proposition is as Lean prints it, checked to elaborate to the same
  term. The source's name, attributes, docstring and proof are not carried over.
-/

import Mathlib

namespace RegistryProblems

/-- OP-00011: A 3 × 3 magic square of distinct squares -/
def Problem_OP_00011 : Prop :=
  ∃ m t,
      Function.Injective2 m ∧
        (∀ (i j : Fin 3), 0 < m i j ∧ IsSquare (m i j)) ∧
          (∀ (i : Fin 3), ∑ j, m i j = t) ∧
            (∀ (j : Fin 3), ∑ i, m i j = t) ∧ m 0 0 + m 1 1 + m 2 2 = t ∧ m 0 2 + m 1 1 + m 2 0 = t

end RegistryProblems
