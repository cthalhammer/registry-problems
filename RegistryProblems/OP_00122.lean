/-
  OP-00122: Finitely many unitary classes with prescribed shifted singular values

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00122

      theorem resolution : RegistryProblems.Problem_OP_00122 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/eigenvalues-and-inverse-problems/SP-15/lean/NLA/SP15/Definitions.lean

  Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The theorem is `¬ CanonicalFiniteness`, so the body is
  CanonicalFiniteness's body; only Square, singularValue, SuperIdentical and
  UnitarySimilar are copied with the file's `open scoped` line, leaving out all
  parameter, block, coefficient, Jacobian and Gram definitions.
-/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Fin.Basic

namespace RegistryProblems.OP_00122
noncomputable section

open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Topology

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Mathlib's genuine decreasing Euclidean singular values, zero extended. -/
def singularValue {n : ℕ} (A : Square n) (k : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues k

/-- The original all-complex-shift, every-ordered-singular-value relation. -/
def SuperIdentical {n : ℕ} (A B : Square n) : Prop :=
  ∀ (z : ℂ) (k : Fin n),
    singularValue (A - z • (1 : Square n)) k.val =
      singularValue (B - z • (1 : Square n)) k.val

/-- Exactly the one-sided unitary condition in the canonical question. -/
def UnitarySimilar {n : ℕ} (A B : Square n) : Prop :=
  ∃ U : Square n, U.conjTranspose * U = 1 ∧ B = U.conjTranspose * A * U

/-- OP-00122: Finitely many unitary classes with prescribed shifted singular values -/
def _root_.RegistryProblems.Problem_OP_00122 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ M : ℕ, 1 ≤ M ∧
    ∀ A : Fin (M + 1) → Square n,
      (∀ i j, SuperIdentical (A i) (A j)) →
        ∃ i j : Fin (M + 1), i < j ∧ UnitarySimilar (A i) (A j)

end
end RegistryProblems.OP_00122
