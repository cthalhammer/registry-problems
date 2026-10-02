/-
  OP-00040: The clique number of Paley graphs

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00040

      theorem resolution : RegistryProblems.Problem_OP_00040 := ...
-/

import Mathlib

namespace RegistryProblems

/-- OP-00040: The clique number of Paley graphs -/
def Problem_OP_00040 : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ p : ℕ, p.Prime → p % 4 = 1 →
  ((SimpleGraph.fromRel fun (x y : ZMod p) => IsSquare (x - y)).cliqueNum : ℝ) ≤
    C * Real.log p ^ k

end RegistryProblems
