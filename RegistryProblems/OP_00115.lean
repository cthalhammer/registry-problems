/-
  OP-00115: Polynomial trace-error factor after exactly the target rank of pivots

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00115

      theorem resolution : RegistryProblems.Problem_OP_00115 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/randomized-and-low-rank-approximation/RA-02/lean/NLA/RA02/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the body of PolynomialTraceFactor copied
  verbatim; quadraticValue, squaredNorm and all witness/proof-support
  definitions after the target (smallParameter … initialLabels) are left out, as
  is the target def itself, and set_option, namespace, noncomputable-section and
  end lines are dropped.
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.OfFn

namespace RegistryProblems.OP_00115
noncomputable section

open scoped BigOperators ComplexOrder Matrix

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev History (n k : ℕ) := Fin k → Fin n

def realTrace {n : ℕ} (A : Square n) : ℝ := A.trace.re

/-- Zero-diagonal choices are harmless totalization. Their probability is zero
for a nonzero PSD residual. The nonzero case is the original complex update. -/
def choleskyStep {n : ℕ} (A : Square n) (j : Fin n) : Square n :=
  if A j j = 0 then A else fun a b => A a b - A a j * A j b / A j j

/-- On a zero PSD residual use uniform dummy labels; all residuals stay zero.
The n=0 value is only totalization: normalization is asserted for n>=1. -/
def pivotMass {n : ℕ} (A : Square n) (j : Fin n) : ℝ :=
  if realTrace A = 0 then 1 / (n : ℝ) else (A j j).re / realTrace A

/-- Chronological residual, including all zero-probability paths. -/
def pathResidual {n : ℕ} (A : Square n) : List (Fin n) → Square n
  | [] => A
  | j :: w => pathResidual (choleskyStep A j) w

/-- Product of actual conditional masses; no independence assumption. -/
def pathWeight {n : ℕ} (A : Square n) : List (Fin n) → ℝ
  | [] => 1
  | j :: w => pivotMass A j * pathWeight (choleskyStep A j) w

def pathContribution {n : ℕ} (A : Square n) (w : List (Fin n)) : ℝ :=
  pathWeight A w * realTrace (pathResidual A w)

/-- Full finite expectation. Every ordered label sequence is included. -/
def expectedTrace {n : ℕ} (A : Square n) (k : ℕ) : ℝ :=
  ∑ f : History n k, pathContribution A (List.ofFn f)

/-- Mathlib's genuinely decreasing eigenvalues. The finite-index transport
uses only card(Fin n)=n; the separately reindexed eigenvalues is not used. -/
def orderedEigenvalues {n : ℕ} (A : Square n) (hA : A.IsHermitian) : Fin n → ℝ :=
  fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

/-- Zero-based i>=r is the original one-based j>r tail. -/
def rankTail {n : ℕ} (A : Square n) (hA : A.IsHermitian) (r : ℕ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i : Fin n => r ≤ i.val), orderedEigenvalues A hA i

/-- OP-00115: Polynomial trace-error factor after exactly the target rank of pivots -/
def _root_.RegistryProblems.Problem_OP_00115 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p : ℝ, 0 ≤ p ∧
    ∀ n : ℕ, 1 ≤ n → ∀ A : Square n, ∀ hA : A.PosSemidef,
      ∀ r : ℕ, 1 ≤ r → r ≤ n →
        expectedTrace A r ≤ C * Real.rpow (r : ℝ) p * rankTail A hA.isHermitian r

end
end RegistryProblems.OP_00115
