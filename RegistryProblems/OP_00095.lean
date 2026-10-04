/-
  OP-00095: Imaginary-part rank in a limiting Green-function matrix equation

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00095

      theorem resolution : RegistryProblems.Problem_OP_00095 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-functions-and-stability/MF-18/lean/NLA/MF18/Definitions.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Only the definitions the body uses (Mat, CPoly,
  regularizedA/B/Q, matrixPolynomial, scalarPencil, unregularizedPolynomial,
  CirclePositive, StrictStable, IsStabilizingSolution, circleRootCount,
  SimpleCircleRoots, hermitianImaginaryPart, GreenAssumptions) are copied with
  the file's `open scoped BigOperators Topology ComplexOrder`, leaving out Vec
  and the homotopy, Cayley, root-count, pairing and stable-subspace definitions;
  the binder theorem canonical_full_complex_rank (implicit n, instance [NeZero
  n]) is turned into a closed Prop that keeps the instance binder.
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank

namespace RegistryProblems.OP_00095
noncomputable section

open scoped BigOperators Topology ComplexOrder

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev CPoly := Polynomial ℂ

def regularizedA {n : ℕ} (C D : Mat n) (η : ℝ) : Mat n :=
  C + (Complex.I * (η : ℂ)) • D

/-- This is generally not the adjoint of regularizedA. -/
def regularizedB {n : ℕ} (C D : Mat n) (η : ℝ) : Mat n :=
  C.conjTranspose + (Complex.I * (η : ℂ)) • D.conjTranspose

def regularizedQ {n : ℕ} (R P : Mat n) (η : ℝ) : Mat n :=
  R + (Complex.I * (η : ℂ)) • P

def matrixPolynomial {n : ℕ} (A B Q : Mat n) : Matrix (Fin n) (Fin n) CPoly :=
  fun i j => Polynomial.C (B i j) * Polynomial.X ^ 2 -
    Polynomial.C (Q i j) * Polynomial.X + Polynomial.C (A i j)

def scalarPencil {n : ℕ} (A B Q : Mat n) : CPoly :=
  (matrixPolynomial A B Q).det

def unregularizedPolynomial {n : ℕ} (C R : Mat n) : CPoly :=
  scalarPencil C C.conjTranspose R

def CirclePositive {n : ℕ} (P D : Mat n) : Prop :=
  ∀ lam : ℂ, ‖lam‖ = 1 → (P + lam • D.conjTranspose + lam⁻¹ • D).PosDef

def StrictStable {n : ℕ} (S : Mat n) : Prop :=
  ∀ lam : ℂ, S.charpoly.IsRoot lam → ‖lam‖ < 1

def IsStabilizingSolution {n : ℕ} (C D R P : Mat n) (η : ℝ) (X : Mat n) : Prop :=
  X.det ≠ 0 ∧
  X + regularizedB C D η * X⁻¹ * regularizedA C D η = regularizedQ R P η ∧
  StrictStable (X⁻¹ * regularizedA C D η)

def circleRootCount (p : CPoly) : ℕ := by
  classical
  exact (p.roots.filter (fun lam => ‖lam‖ = 1)).card

def SimpleCircleRoots (p : CPoly) : Prop :=
  ∀ lam : ℂ, ‖lam‖ = 1 → p.IsRoot lam → p.rootMultiplicity lam = 1

def hermitianImaginaryPart {n : ℕ} (X : Mat n) : Mat n :=
  ((2 * Complex.I : ℂ)⁻¹) • (X - X.conjTranspose)

/-- Only original model assumptions. No rank/count/selection conclusion is a field.
Uniqueness of the given family is not needed for the stronger theorem. -/
def GreenAssumptions {n : ℕ} (C D R P : Mat n) (X : ℝ → Mat n) (X₀ : Mat n) : Prop :=
  R.IsHermitian ∧ P.IsHermitian ∧ CirclePositive P D ∧
  (∀ η : ℝ, 0 < η → IsStabilizingSolution C D R P η (X η)) ∧
  Filter.Tendsto X (nhdsWithin 0 (Set.Ioi 0)) (nhds X₀) ∧
  X₀.det ≠ 0 ∧ unregularizedPolynomial C R ≠ 0 ∧
  SimpleCircleRoots (unregularizedPolynomial C R)

/-- OP-00095: Imaginary-part rank in a limiting Green-function matrix equation -/
def _root_.RegistryProblems.Problem_OP_00095 : Prop :=
  ∀ (n : ℕ) [NeZero n] (C D R P : Mat n) (X : ℝ → Mat n) (X₀ : Mat n) (m : ℕ),
    GreenAssumptions C D R P X X₀ →
    (∀ η : ℝ, 0 < η → ∀ Y : Mat n,
      IsStabilizingSolution C D R P η Y → Y = X η) →
    circleRootCount (unregularizedPolynomial C R) = 2 * m →
    (hermitianImaginaryPart X₀).rank = m

end
end RegistryProblems.OP_00095
