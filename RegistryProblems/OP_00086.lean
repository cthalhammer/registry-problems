/-
  OP-00086: Johnson's derivative-realizability conjecture

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00086

      theorem resolution : RegistryProblems.Problem_OP_00086 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/eigenvalues-and-inverse-problems/IS-03/lean/NLA/IS03/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions of NLA.IS03 that
  DerivativeRealizabilityConjecture uses, moved to this problem's namespace,
  with the conjecture's body as the statement; the witness matrix, polynomials
  and trace moments, which only the proof uses, are left out.
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace

namespace RegistryProblems.OP_00086
noncomputable section

open Matrix Polynomial
open scoped Matrix

/-- Actual real square matrices of the indicated finite order. -/
abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Entrywise nonnegativity; it is not positive-semidefinite order. -/
def EntrywiseNonnegative {n : ℕ} (A : RealMatrix n) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- The actual formal derivative, scaled by the reciprocal of the matrix order. -/
def normalizedDerivative (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ((n : ℝ)⁻¹) • p.derivative

/-- OP-00086: Johnson's derivative-realizability conjecture -/
def _root_.RegistryProblems.Problem_OP_00086 : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ A : RealMatrix n, EntrywiseNonnegative A →
    ∃ B : RealMatrix (n - 1), EntrywiseNonnegative B ∧
      B.charpoly = normalizedDerivative n A.charpoly

end
end RegistryProblems.OP_00086
