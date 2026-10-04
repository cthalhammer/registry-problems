/-
  OP-00098: Sharp additive triangle constant for an odd number of contractions

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00098

      theorem resolution : RegistryProblems.Problem_OP_00098 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-03/lean/NLA/MI03/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Copied Mat through sharpConstant verbatim with their
  open line, left out OddContractionConjecture (its body is the body) and the
  decomposition and witness definitions (pairVariance, shiftedSquare,
  rootOfUnity, firstVector, witnessVector, outerProduct, witness,
  firstProjection, witnessModulusSum, witnessDifference) that only other exports
  use, and dropped set_option autoImplicit false, the namespace and the
  noncomputable section lines.
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace RegistryProblems.OP_00098
noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The actual principal positive square root of the actual Gram matrix. -/
def matrixModulus {n : ℕ} (A : Mat n) : Mat n :=
  CFC.sqrt (A.conjTranspose * A)

/-- The genuine induced Euclidean operator norm, not an entrywise matrix norm. -/
def operatorNorm {n : ℕ} (A : Mat n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖

def summandSum {n k : ℕ} (A : Fin k → Mat n) : Mat n := ∑ j, A j

def modulusSum {n k : ℕ} (A : Fin k → Mat n) : Mat n :=
  ∑ j, matrixModulus (A j)

/-- Positivity of this actual difference is the original matrix-order bound. -/
def errorGap {n k : ℕ} (A : Fin k → Mat n) (c : ℝ) : Mat n :=
  (c : ℂ) • (1 : Mat n) + modulusSum A - matrixModulus (summandSum A)

/-- Every positive dimension and every complex contraction tuple are retained. -/
def AdmissibleConstant (k : ℕ) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ n : ℕ, 1 ≤ n → ∀ A : Fin k → Mat n,
    (∀ j, operatorNorm (A j) ≤ 1) → (errorGap A c).PosSemidef

def admissibleConstants (k : ℕ) : Set ℝ := {c | AdmissibleConstant k c}

/-- The original infimum. Nonemptiness and a least element are proof obligations. -/
def sharpConstant (k : ℕ) : ℝ := sInf (admissibleConstants k)

/-- OP-00098: Sharp additive triangle constant for an odd number of contractions -/
def _root_.RegistryProblems.Problem_OP_00098 : Prop :=
  ∀ k : ℕ, 3 ≤ k → Odd k → sharpConstant k = (k : ℝ) / 4

end
end RegistryProblems.OP_00098
