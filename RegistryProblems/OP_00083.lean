/-
  OP-00083: Sharp inverse norm bound from upper bounds on matrix entries

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00083

      theorem resolution : RegistryProblems.Problem_OP_00083 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/linear-systems-and-elimination/IE-19/lean/NLA/IE19/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Keeps the 4 definitions SharpConjecture uses; leaves
  out LowerBoundConjecture (the inequality-only part, negated by the separate
  export not_lowerBoundConjecture) and the witness matrices; the body is the
  body of def SharpConjecture, verbatim; set_option autoImplicit false and the
  namespace/section lines are dropped.
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00083
noncomputable section

open scoped NNReal

/-- The comparison matrix `α I + m 11ᵀ`; the inequalities in IE-19 are entrywise. -/
def comparisonMatrix {n : ℕ} (α m : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then α else 0) + m

/-- The exact maximum absolute row-sum norm. The finite supremum is taken in `ℝ≥0`
before coercing to `ℝ`; it is zero for an empty matrix. This is not the default
entrywise supremum norm on a matrix. -/
noncomputable def rowSumNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((Finset.univ.sup fun i : Fin n => ∑ j : Fin n, ‖M i j‖₊) : ℝ≥0)

/-- Symmetry, strictly positive entries bounded by the comparison matrix, and
weak diagonal dominance, exactly as in the canonical IE-19 statement. -/
def Admissible {n : ℕ} (α m : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  J.transpose = J ∧
  (∀ i j, 0 < J i j ∧ J i j ≤ comparisonMatrix α m i j) ∧
  (∀ i, (∑ j ∈ Finset.univ.erase i, J i j) ≤ J i i)

/-- The displayed proposed lower bound, with all arithmetic over the reals. -/
def comparisonBound (n : ℕ) (α m : ℝ) : ℝ :=
  (α + 2 * m * ((n : ℝ) - 1)) / (α * (α + m * (n : ℝ)))

/-- OP-00083: Sharp inverse norm bound from upper bounds on matrix entries -/
def _root_.RegistryProblems.Problem_OP_00083 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ α m : ℝ, 0 < m → ((n : ℝ) - 2) * m ≤ α →
    ∀ J : Matrix (Fin n) (Fin n) ℝ, Admissible α m J →
      comparisonBound n α m ≤ rowSumNorm J⁻¹ ∧
      (rowSumNorm J⁻¹ = comparisonBound n α m ↔ J = comparisonMatrix α m)

end
end RegistryProblems.OP_00083
