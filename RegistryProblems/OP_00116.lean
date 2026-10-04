/-
  OP-00116: Improve the randomized LU squared-error factor to 2^k

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00116

      theorem resolution : RegistryProblems.Problem_OP_00116 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/randomized-and-low-rank-approximation/RA-03/lean/NLA/RA03/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the body of SquaredErrorConjecture copied
  verbatim; the witness definitions (witness, witnessGram, witnessPivotMass,
  witnessPivotError) and the target def itself are left out, and set_option,
  namespace and noncomputable-section lines are dropped.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00116
noncomputable section

open scoped BigOperators Classical

/-- The squared Frobenius norm, written as the exact sum of squared complex moduli. -/
def frobeniusSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- `none` is the absorbing label used only after the residual is zero.
Each `some (i,j)` selects a row and a column together. -/
abbrev Pivot (m n : ℕ) := Option (Fin m × Fin n)

/-- The exact conditional pivot probabilities. The zero residual assigns
probability one to `none`; otherwise only entry labels have nonzero mass. -/
def pivotMass {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) : Pivot m n → ℝ
  | none => if S = 0 then 1 else 0
  | some ij => if S = 0 then 0 else Complex.normSq (S ij.1 ij.2) / frobeniusSq S

/-- The canonical rank-one cross update. A zero entry is given an identity
update solely to totalize the function; its selection probability is zero. -/
def pivotResidual {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ)
    (ij : Fin m × Fin n) : Matrix (Fin m) (Fin n) ℂ :=
  if S ij.1 ij.2 = 0 then S
  else fun a b => S a b - S a ij.2 * S ij.1 b / S ij.1 ij.2

/-- The next residual for a transition label. The `none` transition has
positive mass exactly at the zero matrix, where it keeps the residual zero. -/
def nextResidual {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) :
    Pivot m n → Matrix (Fin m) (Fin n) ℂ
  | none => 0
  | some ij => pivotResidual S ij

/-- The terminal residual along an ordered history of `k` transitions. -/
def historyResidual {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) :
    {k : ℕ} → (Fin k → Pivot m n) → Matrix (Fin m) (Fin n) ℂ
  | 0, _ => S
  | k + 1, h => historyResidual (nextResidual S (h 0)) (fun i : Fin k => h i.succ)

/-- The joint probability of a history is the product of the conditional
probabilities along its actual residuals. No independence of row and column
choices, or of successive pivot choices, is assumed. -/
def historyMass {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) :
    {k : ℕ} → (Fin k → Pivot m n) → ℝ
  | 0, _ => 1
  | k + 1, h => pivotMass S (h 0) *
      historyMass (nextResidual S (h 0)) (fun i : Fin k => h i.succ)

/-- The actual finite expectation after exactly `k` transitions. Absorption
implements the canonical instruction to keep all later residuals zero. -/
def expectedError {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) : ℝ :=
  ∑ h : Fin k → Pivot m n, historyMass A h * frobeniusSq (historyResidual A h)

/-- The decreasing singular values of the matrix acting on complex Euclidean
spaces, using mathlib's zero-based sequence with its actual spectral definition. -/
def singularValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues j

/-- The canonical squared singular-value tail after rank `k`.
Paper indices `j > k` become zero-based indices in `[k, min m n)`. -/
def singularTailSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico k (min m n), singularValue A j ^ 2

/-- OP-00116: Improve the randomized LU squared-error factor to 2^k -/
def _root_.RegistryProblems.Problem_OP_00116 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℂ,
    ∀ k : ℕ, 1 ≤ k → k ≤ min m n →
      expectedError A k ≤ (2 : ℝ) ^ k * singularTailSq A k

end
end RegistryProblems.OP_00116
