/-
  OP-00112: The nonnegative rank of the nine-point distance matrix

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00112

      theorem resolution : RegistryProblems.Problem_OP_00112 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/nonnegative-and-positive-factorizations/NR-04/lean/NLA/NR04/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The theorem states the problem inline (¬ ∃ W H, ...),
  so the body is that existence statement, copied verbatim, and the preamble is
  only the one definition it uses, distanceNine; left out as unused by it:
  EntrywiseNonnegative, HasNonnegativeFactorization, firstThree, center, label,
  upperW, upperH, ColumnStochastic, columnSet, columnHull, columnAffineSpan,
  columnSection; their namespace, noncomputable-section, set_option and open
  lines are dropped (the body needs none of them).
-/

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace RegistryProblems.OP_00112
noncomputable section

/-- The canonical nine-point squared-distance matrix, with zero-based indices. -/
def distanceNine : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => ((i.val : ℝ) - (j.val : ℝ)) ^ 2

/-- OP-00112: The nonnegative rank of the nine-point distance matrix -/
def _root_.RegistryProblems.Problem_OP_00112 : Prop :=
  ∃ W : Matrix (Fin 9) (Fin 6) ℝ,
      ∃ H : Matrix (Fin 6) (Fin 9) ℝ,
        (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧
          W * H = distanceNine

end
end RegistryProblems.OP_00112
