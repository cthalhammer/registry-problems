/-
  OP-00081: Monotonic optimal backward error along LSMR

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00081

      theorem resolution : RegistryProblems.Problem_OP_00081 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/linear-systems-and-elimination/IE-17/lean/NLA/IE17/Definitions.lean

  Copyright (c) 2026 George Stepaniants.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Keeps the 15 definitions the two monotonicity
  conjectures use; leaves out the witness data (witnessA, witnessB, witnessX₁-₃,
  witnessRun); the body is the conjunction of the bodies of
  OptimalErrorsNonincreasing and ApproximationErrorsNonincreasing, each copied
  verbatim inside parentheses; the namespace/section lines are dropped.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00081
noncomputable section

open Matrix

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The induced Euclidean operator norm, with both spaces carrying their L2 norms. -/
def spectralNorm {m n : ℕ} (A : Mat m n) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

def residual {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : Vec m :=
  b - A.toEuclideanLin x

def normalResidual {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : Vec n :=
  A.transpose.toEuclideanLin (residual A b x)

/-- Only the matrix is perturbed; b is kept fixed. -/
def Feasible {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) (E : Mat m n) : Prop :=
  normalResidual (A + E) b x = 0

def errorSet {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : Set ℝ :=
  {δ | ∃ E : Mat m n, Feasible A b x E ∧ spectralNorm E = δ}

/-- A minimum, including actual attainment, not merely an infimum. -/
def IsOptimalError {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) (δ : ℝ) : Prop :=
  IsLeast (errorSet A b x) δ

/-- K_k(AᵀA,Aᵀb), with K_0={0}. -/
def krylov {m n : ℕ} (A : Mat m n) (b : Vec m) (k : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ {v | ∃ j : ℕ, j < k ∧
    v = ((A.transpose * A) ^ j).toEuclideanLin (A.transpose.toEuclideanLin b)}

/-- Exact normal-residual minimization and the specified minimum-length convention. -/
def IsLSMRIterate {m n : ℕ} (A : Mat m n) (b : Vec m) (k : ℕ) (x : Vec n) : Prop :=
  x ∈ krylov A b k ∧
  (∀ y ∈ krylov A b k, ‖normalResidual A b x‖ ≤ ‖normalResidual A b y‖) ∧
  (∀ y ∈ krylov A b k, ‖normalResidual A b y‖ = ‖normalResidual A b x‖ → ‖x‖ ≤ ‖y‖)

/-- A complete finite exact run from zero through its first least-squares solution. -/
def IsTerminatingLSMRRun {m n N : ℕ} (A : Mat m n) (b : Vec m)
    (xs : Fin (N + 1) → Vec n) : Prop :=
  xs 0 = 0 ∧ (∀ k, IsLSMRIterate A b k.val (xs k)) ∧
  (∀ k, k.val < N → normalResidual A b (xs k) ≠ 0) ∧
  normalResidual A b (xs (Fin.last N)) = 0

/-- Four real Moore–Penrose equations; no nonsingular-inverse substitute. -/
def IsMoorePenrose {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (K : Matrix ι κ ℝ) (P : Matrix κ ι ℝ) : Prop :=
  K * P * K = K ∧ P * K * P = P ∧ (K * P).transpose = K * P ∧
    (P * K).transpose = P * K

/-- The canonical stacked matrix [A; (‖r‖₂/‖x‖₂)I]. -/
def stacked {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    Matrix (Fin m ⊕ Fin n) (Fin n) ℝ :=
  fun i j => match i with
    | Sum.inl i => A i j
    | Sum.inr i => if i = j then ‖residual A b x‖ / ‖x‖ else 0

def stackedResidual {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    EuclideanSpace ℝ (Fin m ⊕ Fin n) :=
  WithLp.toLp 2 (fun i => match i with
    | Sum.inl i => residual A b x i
    | Sum.inr _ => 0)

/-- The canonical approximation on nonzero iterates, with its exact-LS zero convention.
The complete target also requires uniqueness, so no choice of generalized inverse changes q. -/
def IsApproximation {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) (q : ℝ) : Prop :=
  x ≠ 0 ∧ if normalResidual A b x = 0 then q = 0 else
    ∃ P : Matrix (Fin n) (Fin m ⊕ Fin n) ℝ,
      IsMoorePenrose (stacked A b x) P ∧
      q = ‖((stacked A b x) * P).toEuclideanLin (stackedResidual A b x)‖ / ‖x‖

/-- OP-00081: Monotonic optimal backward error along LSMR -/
def _root_.RegistryProblems.Problem_OP_00081 : Prop :=
  (∀ (m n N : ℕ) (A : Mat m n) (b : Vec m) (xs : Fin (N + 1) → Vec n),
    IsTerminatingLSMRRun A b xs →
    ∀ (i j : Fin (N + 1)), j.val = i.val + 1 → xs i ≠ 0 → xs j ≠ 0 →
    ∀ (μ ν : ℝ), IsOptimalError A b (xs i) μ → IsOptimalError A b (xs j) ν → ν ≤ μ) ∧
  (∀ (m n N : ℕ) (A : Mat m n) (b : Vec m) (xs : Fin (N + 1) → Vec n),
    IsTerminatingLSMRRun A b xs →
    ∀ (i j : Fin (N + 1)), j.val = i.val + 1 → xs i ≠ 0 → xs j ≠ 0 →
    ∀ (μ ν : ℝ), IsApproximation A b (xs i) μ → IsApproximation A b (xs j) ν → ν ≤ μ)

end
end RegistryProblems.OP_00081
