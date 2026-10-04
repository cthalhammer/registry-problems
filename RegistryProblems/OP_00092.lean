/-
  OP-00092: Uniform polynomial bounds for products at joint spectral radius one

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00092

      theorem resolution : RegistryProblems.Problem_OP_00092 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-functions-and-stability/MF-07/lean/NLA/MF07/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Only the definitions the body uses (Square,
  spectralNorm, matrixProduct, finiteProduct, WordIn, familyNorm, wordNorms,
  familyGrowth, rootGrowth, jointSpectralRadius) are copied, leaving out
  EuclideanVector, applyMatrix, IsComplexNorm, IsUnitary, the diagonal-weight,
  damping and constant definitions; the binder theorem canonical_uniform_bound
  is turned into a closed Prop.
-/

import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.OfFn
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace RegistryProblems.OP_00092
noncomputable section

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Actual complex Euclidean operator norm, with no default entrywise norm. -/
def spectralNorm {d : ℕ} (A : Square d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A‖

/-- Chronological order: later factors act on the left. -/
def matrixProduct {d : ℕ} (w : List (Square d)) : Square d := w.reverse.prod

def finiteProduct {d n : ℕ} (A : Fin n → Square d) : Square d :=
  matrixProduct (List.ofFn A)

def WordIn {d : ℕ} (M : Set (Square d)) (w : List (Square d)) : Prop :=
  ∀ A ∈ w, A ∈ M

/-- The actual supremum; compact attainment is an independent obligation. -/
def familyNorm {d : ℕ} (M : Set (Square d)) : ℝ := sSup (spectralNorm '' M)

/-- All words are retained, including repetitions and infinitely many possible
generators. This is not a finite-generator restriction. -/
def wordNorms {d : ℕ} (M : Set (Square d)) (n : ℕ) : Set ℝ :=
  {r | ∃ w : List (Square d), w.length = n ∧ WordIn M w ∧
    r = spectralNorm (matrixProduct w)}

def familyGrowth {d : ℕ} (M : Set (Square d)) (n : ℕ) : ℝ := sSup (wordNorms M n)

/-- The n=0 value is immaterial to the limit and excluded from the infimum. -/
def rootGrowth {d : ℕ} (M : Set (Square d)) (n : ℕ) : ℝ :=
  Real.rpow (familyGrowth M n) (1 / (n : ℝ))

/-- Fekete's infimum formula. Its radius-one equivalence with the canonical
root limit is mandatory; no radius is assigned by definition. -/
def jointSpectralRadius {d : ℕ} (M : Set (Square d)) : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = rootGrowth M n}

/-- OP-00092: Uniform polynomial bounds for products at joint spectral radius one -/
def _root_.RegistryProblems.Problem_OP_00092 : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∃ Θ : ℝ, 0 < Θ ∧ ∀ M : Set (Square d), IsCompact M → M.Nonempty →
      jointSpectralRadius M = 1 → ∀ n : ℕ, 1 ≤ n → ∀ A : Fin n → Square d,
      (∀ i, A i ∈ M) →
      spectralNorm (finiteProduct A) ≤ Θ * (familyNorm M * (n : ℝ)) ^ (d - 1)

end
end RegistryProblems.OP_00092
