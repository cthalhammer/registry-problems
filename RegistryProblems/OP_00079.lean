/-
  OP-00079: Exact extremizers for partial pivoting on orthogonal matrices

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00079

      theorem resolution : RegistryProblems.Problem_OP_00079 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/linear-systems-and-elimination/IE-05/lean/NLA/IE05/Definitions.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Keeps the 22 definitions
  OrthogonalExtremizerConjecture uses; leaves out IntMat, UpperTriangular,
  UnitLower, candidateR, PositiveQR, FirstAvailablePivot/FirstAvailablePath,
  noSwapPath, activeMax, scaledColumns, tailProduct and all integer witness
  data; the body is the body of def OrthogonalExtremizerConjecture, verbatim;
  the namespace/section lines are dropped.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace RegistryProblems.OP_00079
noncomputable section

open scoped BigOperators NNReal

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

abbrev PivotPath (n : ℕ) := Fin n → Fin n

/-- Actual real column orthogonality, with no spectral or pivot assumptions. -/
def Orthogonal {n : ℕ} (A : Mat n) : Prop := A.transpose * A = 1

def prescribedLower (n : ℕ) : Mat n :=
  fun i j => if i = j then 1 else if j < i then -1 else 0

/-- These are L2 Euclidean columns, not the coordinatewise supremum norm. -/
def euclideanColumns {n : ℕ} (A : Mat n) : Fin n → EuclideanSpace ℝ (Fin n) :=
  fun j => WithLp.toLp 2 (fun i => A i j)

/-- Mathlib's normalized Gram--Schmidt, in the usual increasing `Fin n` order. -/
def normalizedQRQ {n : ℕ} (A : Mat n) : Mat n :=
  fun i j => InnerProductSpace.gramSchmidtNormed ℝ (euclideanColumns A) j i

def candidateQ (n : ℕ) : Mat n := normalizedQRQ (prescribedLower n)

/-- Swap the current row positions; no column exchange occurs in partial pivoting. -/
def rowSwap {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  fun i j => S (Equiv.swap k p i) j

/-- The actual Schur update, padded by zero outside the new active trailing block.
Division is total in Lean; `AdmissiblePivot` separately requires a nonzero pivot. -/
def schurStep {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  let B := rowSwap S k p
  fun i j => if k < i ∧ k < j then
    B i j - (B i k / B k k) * B k j else 0

/-- Stage zero is the input; stages `0,...,n-1` are the active Schur complements. -/
def trajectory {n : ℕ} (A : Mat n) (path : PivotPath n) : ℕ → Mat n
  | 0 => A
  | k + 1 => if h : k < n then
      schurStep (trajectory A path k) ⟨k, h⟩ (path ⟨k, h⟩) else 0

def AdmissiblePivot {n : ℕ} (S : Mat n) (k p : Fin n) : Prop :=
  k ≤ p ∧ S p k ≠ 0 ∧ ∀ i, k ≤ i → |S i k| ≤ |S p k|

def AdmissiblePath {n : ℕ} (A : Mat n) (path : PivotPath n) : Prop :=
  ∀ k, AdmissiblePivot (trajectory A path k.val) k (path k)

/-- A deterministic ascending-row scan. Equal magnitudes never replace the current row. -/
def firstPivotIndex {n : ℕ} (S : Mat n) (k : Fin n) : Fin n :=
  (List.finRange n).foldl
    (fun p i => if k ≤ i ∧ |S p k| < |S i k| then i else p) k

def firstTrajectory {n : ℕ} (A : Mat n) : ℕ → Mat n
  | 0 => A
  | k + 1 => if h : k < n then
      schurStep (firstTrajectory A k) ⟨k, h⟩
        (firstPivotIndex (firstTrajectory A k) ⟨k, h⟩) else 0

def firstPath {n : ℕ} (A : Mat n) : PivotPath n :=
  fun k => firstPivotIndex (firstTrajectory A k.val) k

/-- Finite maximum of absolute real entries, implemented as a supremum in `ℝ≥0`. -/
def entryMaxNN {n : ℕ} (A : Mat n) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊)

def entryMax {n : ℕ} (A : Mat n) : ℝ := entryMaxNN A

def activeMaxNN {n : ℕ} (S : Mat n) (k : ℕ) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n =>
    if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)

/-- All and only the `n` active stages enter the growth numerator. -/
def growth {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n =>
    activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ) / entryMax A

def firstGrowth {n : ℕ} (A : Mat n) : ℝ := growth A (firstPath A)

/-- Every orthogonal input and every admissible partial-pivoting path is included. -/
def orthogonalGrowthSet (n : ℕ) : Set ℝ :=
  {r | ∃ A : Mat n, Orthogonal A ∧
    ∃ path : PivotPath n, AdmissiblePath A path ∧ r = growth A path}

/-- The actual conditionally complete real supremum. No boundedness is assumed here. -/
def orthogonalGrowthSup (n : ℕ) : ℝ := sSup (orthogonalGrowthSet n)

/-- OP-00079: Exact extremizers for partial pivoting on orthogonal matrices -/
def _root_.RegistryProblems.Problem_OP_00079 : Prop :=
  ∀ n : ℕ, 2 ≤ n → orthogonalGrowthSup n = firstGrowth (candidateQ n)

end
end RegistryProblems.OP_00079
