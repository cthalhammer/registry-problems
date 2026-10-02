/-
  OP-00032: The Hadamard conjecture

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00032

      theorem resolution : RegistryProblems.Problem_OP_00032 := ...

  Formalised by The Formal Conjectures Authors, not by clopen.solutions:
  https://github.com/google-deepmind/formal-conjectures/blob/137aec5c7abd3aa61f7a73138a97279acfc79e93/FormalConjectures/Wikipedia/Hadamard.lean#L90

  Copyright 2025 The Formal Conjectures Authors.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The statement is the source theorem
  HadamardConjecture's proposition, quantified over its parameter k, with the
  source's definition IsHadamard (entries in {1, -1} and |det M| = n^(n/2))
  unfolded. The source's name, attributes, docstring and proof are not carried
  over.
-/

import Mathlib

namespace RegistryProblems

/-- OP-00032: The Hadamard conjecture -/
def Problem_OP_00032 : Prop :=
  ∀ (k : ℕ), ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
  (∀ (i j : Fin (4 * k)), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2)

end RegistryProblems
