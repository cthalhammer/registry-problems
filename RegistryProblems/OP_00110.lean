/-
  OP-00110: The Rowland–Wu polynomial identity for Sinkhorn limits

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00110

      theorem resolution : RegistryProblems.Problem_OP_00110 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/nonnegative-and-positive-factorizations/NM-04/lean/NLA/NM04/Definitions.lean

  Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Their `attribute [local instance]
  Classical.propDecidable` (refused by our preamble rules) is replaced by an
  equivalent local instance of the same classical decision procedure at the same
  default priority; their namespace, noncomputable-section, set_option and
  closing end lines are dropped; the binder theorem rowland_wu_identity becomes
  a closed Prop with its binders kept as written (m n implicit; hA turned into
  an arrow); left out as unused by it: emptyIndex, erasedIndex, cofactorForm,
  lowering, raising, columnExchange, rowExchange, borderedMatrix, pencil,
  weight, rowPartition, potential, columnImbalance, meanZero, rowNormalized,
  schurTail, covarianceFactor.
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Order.Compact

namespace RegistryProblems.OP_00110
noncomputable section

open scoped BigOperators Matrix

/-- Stands in for the source's `attribute [local instance] Classical.propDecidable`, which
registers the classical decision procedure at default priority: the same instance, at the
same priority, so the definitions below elaborate with the same decidability instances. -/
noncomputable local instance (priority := default) propDecidableDefault (a : Prop) : Decidable a :=
  Classical.propDecidable a

universe u v w
variable {α : Type u} {β : Type v} {𝕜 : Type w}

/-- A pair of actual finite subsets with equal cardinalities. -/
abbrev MinorIndex (α : Type u) (β : Type v) :=
  {RC : Finset α × Finset β // RC.1.card = RC.2.card}

/-- One-based position in the increasing order. Only member positions enter signs. -/
def position [LinearOrder α] (s : α) (U : Finset α) : ℕ :=
  (U.filter (fun t => t < s)).card + 1

/-- The two maps enumerate the selected rows and columns in increasing order. -/
def minorMatrix [LinearOrder α] [LinearOrder β]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    Matrix (Fin I.1.1.card) (Fin I.1.1.card) 𝕜 :=
  fun i j => T (I.1.1.orderEmbOfFin rfl i)
    (I.1.2.orderEmbOfFin I.property.symm j)

def minor [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) : 𝕜 :=
  (minorMatrix T I).det

/-- Literal singleton supports from the canonical four off-diagonal cases. -/
def RaisingSupport [DecidableEq α] [DecidableEq β]
    (I J : MinorIndex α β) (s : α) (t : β) : Prop :=
  I.1.1 \ J.1.1 = ∅ ∧ J.1.1 \ I.1.1 = {s} ∧
  I.1.2 \ J.1.2 = ∅ ∧ J.1.2 \ I.1.2 = {t}

def LoweringSupport [DecidableEq α] [DecidableEq β]
    (I J : MinorIndex α β) (s : α) (t : β) : Prop :=
  I.1.1 \ J.1.1 = {s} ∧ J.1.1 \ I.1.1 = ∅ ∧
  I.1.2 \ J.1.2 = {t} ∧ J.1.2 \ I.1.2 = ∅

def ColumnExchangeSupport [DecidableEq α] [DecidableEq β]
    (I J : MinorIndex α β) (s t : β) : Prop :=
  I.1.1 \ J.1.1 = ∅ ∧ J.1.1 \ I.1.1 = ∅ ∧
  I.1.2 \ J.1.2 = {s} ∧ J.1.2 \ I.1.2 = {t}

def RowExchangeSupport [DecidableEq α] [DecidableEq β]
    (I J : MinorIndex α β) (s t : α) : Prop :=
  I.1.1 \ J.1.1 = {s} ∧ J.1.1 \ I.1.1 = {t} ∧
  I.1.2 \ J.1.2 = ∅ ∧ J.1.2 \ I.1.2 = ∅

def raisingCoefficient [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
    (I J : MinorIndex α β) : ℤ :=
  ∑ s : α, ∑ t : β, if RaisingSupport I J s t then
    (-1) ^ (position s J.1.1 + position t J.1.2) else 0

def loweringCoefficient [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
    (I J : MinorIndex α β) : ℤ :=
  ∑ s : α, ∑ t : β, if LoweringSupport I J s t then
    (-1) ^ (position s I.1.1 + position t I.1.2) else 0

def columnExchangeCoefficient [Fintype β] [DecidableEq α] [LinearOrder β]
    (I J : MinorIndex α β) : ℤ :=
  ∑ s : β, ∑ t : β, if ColumnExchangeSupport I J s t then
    (-1) ^ (position s I.1.2 + position t J.1.2) else 0

def rowExchangeCoefficient [Fintype α] [LinearOrder α] [DecidableEq β]
    (I J : MinorIndex α β) : ℤ :=
  ∑ s : α, ∑ t : α, if RowExchangeSupport I J s t then
    (-1) ^ (position s I.1.1 + position t J.1.1) else 0

abbrev Rect (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- Original labels 2,...,m, stored as their zero-based `Fin m` indices. -/
abbrev Tail (m : ℕ) := {i : Fin m // 0 < i.val}
abbrev Index (m n : ℕ) := MinorIndex (Tail m) (Tail n)

def firstIndex {m : ℕ} (hm : 1 ≤ m) : Fin m := ⟨0, hm⟩

def tailMatrix {m n : ℕ} (A : Rect m n) : Matrix (Tail m) (Tail n) ℝ :=
  fun i j => A i.val j.val

/-- First index followed by increasing tail indices is the source's increasing order. -/
def delta {m n : ℕ} (A : Rect m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (I : Index m n) : ℝ :=
  Matrix.det (A.submatrix
    (Fin.cons (firstIndex hm) (fun i => (I.1.1.orderEmbOfFin rfl i).val))
    (Fin.cons (firstIndex hn) (fun j => (I.1.2.orderEmbOfFin I.property.symm j).val)))

def gamma {m n : ℕ} (A : Rect m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (I : Index m n) : ℝ :=
  A (firstIndex hm) (firstIndex hn) * minor (tailMatrix A) I

/-- Integer arithmetic, including the negative diagonal and lowering coefficient. -/
def H (m n : ℕ) : Matrix (Index m n) (Index m n) ℤ :=
  fun I J => if I = J then
    (I.1.1.card : ℤ) * ((m : ℤ) + (n : ℤ)) - (m : ℤ) * (n : ℤ)
  else (m : ℤ) * raisingCoefficient I J - (n : ℤ) * loweringCoefficient I J +
    (m : ℤ) * columnExchangeCoefficient I J + (n : ℤ) * rowExchangeCoefficient I J

def HReal (m n : ℕ) : Matrix (Index m n) (Index m n) ℝ :=
  fun I J => (H m n I J : ℝ)

def Positive {m n : ℕ} (A : Rect m n) : Prop := ∀ i j, 0 < A i j

def Balanced {m n : ℕ} (S : Rect m n) : Prop :=
  (∀ i, ∑ j, S i j = 1) ∧ (∀ j, ∑ i, S i j = (m : ℝ) / (n : ℝ))

/-- Entrywise form of multiplication by the actual two diagonal matrices. -/
def diagonalScale {m n : ℕ} (A : Rect m n) (a : Fin m → ℝ)
    (b : Fin n → ℝ) : Rect m n := fun i j => a i * A i j * b j

def ScaledBalanced {m n : ℕ} (A S : Rect m n) : Prop :=
  ∃ (a : Fin m → ℝ) (b : Fin n → ℝ),
    (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧ S = diagonalScale A a b ∧ Balanced S

/-- Total choice only. Existence, uniqueness and exclusion of the fallback on
    positive inputs are separate contracts and are not assumptions of this definition. -/
def sinkhorn {m n : ℕ} (A : Rect m n) : Rect m n :=
  if h : ∃ S, ScaledBalanced A S then Classical.choose h else 0

/-- OP-00110: The Rowland–Wu polynomial identity for Sinkhorn limits -/
def _root_.RegistryProblems.Problem_OP_00110 : Prop :=
  ∀ {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (A : Rect m n), Positive A →
    (∑ E : Finset (Index m n),
      ((m : ℝ)⁻¹ • (HReal m n).submatrix
        (Subtype.val : E → Index m n) (Subtype.val : E → Index m n)).det *
      (∏ I ∈ E, delta A hm hn I) * (∏ I ∈ (Finset.univ \ E), gamma A hm hn I) *
      ((sinkhorn A) (firstIndex hm) (firstIndex hn)) ^ E.card) = 0

end
end RegistryProblems.OP_00110
