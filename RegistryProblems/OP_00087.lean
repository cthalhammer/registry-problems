/-
  OP-00087: Polynomial-size vertex test for inverse M-matrix intervals

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00087

      theorem resolution : RegistryProblems.Problem_OP_00087 := ...

  Formalised by Sidney Holden, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/intervals-and-absolute-value-equations/IV-03/lean/NLA/IV03/Definitions.lean

  Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions TwoSignCriterion uses are copied
  verbatim without their namespace, noncomputable-section and set_option lines;
  the TwoSignCriterion def itself becomes the body; nothing else is left out
  (every definition in the file is in the body's closure).
-/

import Mathlib

namespace RegistryProblems.OP_00087
noncomputable section

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- An actual nonsingular, entrywise nonnegative matrix whose inverse has
nonpositive off-diagonal entries. No regularity of a whole interval is assumed. -/
def IsInverseM {n : ℕ} (A : Mat n) : Prop :=
  IsUnit A ∧ (∀ i j, 0 ≤ A i j) ∧ ∀ i j, i ≠ j → A⁻¹ i j ≤ 0

def OrderedEndpoints {n : ℕ} (L U : Mat n) : Prop := ∀ i j, L i j ≤ U i j

def intervalFamily {n : ℕ} (L U : Mat n) : Set (Mat n) :=
  {A | ∀ i j, L i j ≤ A i j ∧ A i j ≤ U i j}

def center {n : ℕ} (L U : Mat n) : Mat n := fun i j => (L i j + U i j) / 2
def radius {n : ℕ} (L U : Mat n) : Mat n := fun i j => (U i j - L i j) / 2

def signVector {n : ℕ} (i : Fin n) (k : Fin n) : ℝ := if k = i then -1 else 1

/-- Entrywise expression for C+s D_i R D_j, with the exact original D_i. -/
def vertex {n : ℕ} (L U : Mat n) (s : ℝ) (i j : Fin n) : Mat n :=
  fun k l => center L U k l + s * signVector i k * radius L U k l * signVector j l

/-- OP-00087: Polynomial-size vertex test for inverse M-matrix intervals -/
def _root_.RegistryProblems.Problem_OP_00087 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ L U : Mat n, OrderedEndpoints L U →
    ((∀ A ∈ intervalFamily L U, IsInverseM A) ↔
      ∀ i j : Fin n, ∀ s ∈ ({(-1 : ℝ), 1} : Set ℝ), IsInverseM (vertex L U s i j))

end
end RegistryProblems.OP_00087
