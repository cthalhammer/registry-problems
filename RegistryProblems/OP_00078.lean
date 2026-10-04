/-
  OP-00078: Exponential smoothed tail bounds for partial pivoting

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00078

      theorem resolution : RegistryProblems.Problem_OP_00078 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/linear-systems-and-elimination/IE-04/lean/NLA/IE04/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Keeps the 16 definitions UniformExponentialTail uses
  plus the measurableSpaceMat instance (not referenced by name, but it supplies
  the MeasurableSpace (Mat n) that gaussianMatrix and AdmissibleRule need);
  leaves out the first-available-path helpers, noSwapPath, activeMax,
  firstGrowth and all witness, box and scalar constants; the body is the body of
  def UniformExponentialTail, verbatim; set_option autoImplicit false and the
  namespace/section lines are dropped.
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

namespace RegistryProblems.OP_00078
noncomputable section

open scoped BigOperators NNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

abbrev PivotPath (n : ℕ) := Fin n → Fin n

/-- The standard nested product measurable space on the actual n² real entries.
Matrix is a type synonym for the double function space; making this instance
explicit does not change its measurable sets or the Gaussian product law. -/
instance measurableSpaceMat (n : ℕ) : MeasurableSpace (Mat n) :=
  (inferInstance : MeasurableSpace (Fin n → Fin n → ℝ))

/-- The actual induced Euclidean matrix norm, fixed by L2Operator scope. -/
def spectralNorm {n : ℕ} (A : Mat n) : ℝ := ‖A‖

/-- Swap current row positions; partial pivoting never exchanges columns. -/
def rowSwap {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  fun i j => S (Equiv.swap k p i) j

/-- Actual Schur update, padded with zero outside the new active block.
Lean's total division is used only to make this a total function; admissible
paths separately require nonzero pivots. -/
def schurStep {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  let B := rowSwap S k p
  fun i j => if k < i ∧ k < j then
    B i j - (B i k / B k k) * B k j else 0

def trajectory {n : ℕ} (A : Mat n) (path : PivotPath n) : ℕ → Mat n
  | 0 => A
  | k + 1 => if h : k < n then
      schurStep (trajectory A path k) ⟨k, h⟩ (path ⟨k, h⟩) else 0

def AdmissiblePivot {n : ℕ} (S : Mat n) (k p : Fin n) : Prop :=
  k ≤ p ∧ S p k ≠ 0 ∧ ∀ i, k ≤ i → |S i k| ≤ |S p k|

def AdmissiblePath {n : ℕ} (A : Mat n) (path : PivotPath n) : Prop :=
  ∀ k, AdmissiblePivot (trajectory A path k.val) k (path k)

/-- The true maximum of absolute input entries, as a finite NNReal supremum. -/
def entryMaxNN {n : ℕ} (A : Mat n) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊)

def entryMax {n : ℕ} (A : Mat n) : ℝ := entryMaxNN A

def activeMaxNN {n : ℕ} (S : Mat n) (k : ℕ) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n =>
    if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)

/-- The exact n active stages are counted, divided by the original entry max. -/
def growth {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n =>
    activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ) / entryMax A

/-- A deterministic measurable GEPP tie rule, valid on every nonsingular input.
The frozen Challenge separately proves that firstPath supplies such a rule;
the quantified class cannot silently be empty. -/
def AdmissibleRule {n : ℕ} (rule : Mat n → PivotPath n) : Prop :=
  (∀ A, A.det ≠ 0 → AdmissiblePath A (rule A)) ∧
    Measurable (fun A => growth A (rule A))

/-- n² mutually independent standard real Gaussians, specified by their actual
finite product measure, not by a premise about unspecified random variables. -/
def gaussianMatrix (n : ℕ) : Measure (Mat n) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1))

def smoothedInput {n : ℕ} (center : Mat n) (σ : ℝ) (G : Mat n) : Mat n :=
  center + σ • G

/-- An actual algorithmic tail event on the nonsingular input domain.
Its measurability is a separate exported obligation. Intersecting with this
domain only decreases any total-extension tail event, so a violation here also
violates any such extension without requiring a singular-set nullity premise. -/
def exceedanceEvent {n : ℕ} (center : Mat n) (σ threshold : ℝ)
    (rule : Mat n → PivotPath n) : Set (Mat n) :=
  {G | let A := smoothedInput center σ G
    A.det ≠ 0 ∧ threshold < growth A (rule A)}

/-- OP-00078: Exponential smoothed tail bounds for partial pivoting -/
def _root_.RegistryProblems.Problem_OP_00078 : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ n : ℕ, 1 ≤ n → ∀ center : Mat n, spectralNorm center ≤ 1 →
      ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ x : ℝ, 1 ≤ x →
        ∀ rule : Mat n → PivotPath n, AdmissibleRule rule →
          gaussianMatrix n (exceedanceEvent center σ
            (x * ((n : ℝ) / σ) ^ c₁) rule) ≤
              ENNReal.ofReal ((2 : ℝ) ^ (-c₂ * x))

end
end RegistryProblems.OP_00078
