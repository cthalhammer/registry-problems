/-
  OP-00004: Primes of the form n² + 1

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00004

      theorem resolution : RegistryProblems.Problem_OP_00004 := ...

  Formalised by The Formal Conjectures Authors, not by clopen.solutions:
  https://github.com/google-deepmind/formal-conjectures/blob/0771383387505c96d1b2f6a3d35088ad00892c5c/FormalConjectures/Wikipedia/PrimesAndPerfectSquares.lean#L31

  Copyright 2025 The Formal Conjectures Authors.
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

/-- OP-00004: Primes of the form n² + 1 -/
def Problem_OP_00004 : Prop :=
  {n | Prime (n ^ 2 + 1)}.Infinite

end RegistryProblems
