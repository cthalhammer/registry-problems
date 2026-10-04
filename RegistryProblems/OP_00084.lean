/-
  OP-00084: Uniqueness of the right inverse minimizing an induced p-to-2 norm

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00084

      theorem resolution : RegistryProblems.Problem_OP_00084 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/linear-systems-and-elimination/IE-23/lean/NLA/IE23/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Keeps the 9 definitions RightInverseUniqueConjecture
  uses; leaves out IsNormMinimizer, rightInverseNorms and the witness data; the
  body is the body of def RightInverseUniqueConjecture, verbatim; set_option
  autoImplicit false and the namespace/section lines are dropped.
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank

namespace RegistryProblems.OP_00084
noncomputable section

open scoped BigOperators Classical

abbrev Vec (n : ℕ) := Fin n → ℂ

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ

/-- The genuine complex Euclidean norm, rather than the default supremum
norm on a function space. -/
def euclideanNorm {n : ℕ} (y : Vec n) : ℝ :=
  ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖

/-- The original finite-real-p denominator, defined by the displayed sum and
real power. The canonical conjecture uses only 2 < p, so neither p=2 nor an
infinite-p endpoint is silently included. Positivity for nonzero vectors is a
theorem obligation, not a premise added to the conjecture. -/
def lpNorm {n : ℕ} (p : ℝ) (y : Vec n) : ℝ :=
  (∑ i, ‖y i‖ ^ p) ^ (1 / p)

/-- Every actual ratio from a nonzero right-hand side. Matrix multiplication
acts on the input vector before taking its Euclidean norm. -/
def ratioSet {m n : ℕ} (p : ℝ) (X : Mat n m) : Set ℝ :=
  {r | ∃ y : Vec m, y ≠ 0 ∧ r = euclideanNorm (X.mulVec y) / lpNorm p y}

/-- The genuine supremum in the canonical definition. Generic nonemptiness,
boundedness, and the least-upper-bound property must all be proved on the
original domain; no default value of a conditional supremum is used as a
counterexample. -/
def inducedNorm {m n : ℕ} (p : ℝ) (X : Mat n m) : ℝ := sSup (ratioSet p X)

/-- Actual matrix rank, equal to the dimension of the complex linear range. -/
def FullRowRank {m n : ℕ} (A : Mat m n) : Prop := A.rank = m

/-- The Moore-Penrose formula used in the canonical full-row-rank statement,
with Mathlib's genuine totalized matrix inverse. Invertibility and the exact
inverse value for the witness must be established; no proposed inverse is
substituted into this definition. -/
def moorePenrose {m n : ℕ} (A : Mat m n) : Mat n m :=
  A.conjTranspose * (A * A.conjTranspose)⁻¹

def IsRightInverse {m n : ℕ} (A : Mat m n) (X : Mat n m) : Prop := A * X = 1

/-- OP-00084: Uniqueness of the right inverse minimizing an induced p-to-2 norm -/
def _root_.RegistryProblems.Problem_OP_00084 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → m < n → ∀ A : Mat m n, FullRowRank A →
    ∀ p : ℝ, 2 < p → ∀ X : Mat n m,
      IsRightInverse A X → X ≠ moorePenrose A →
        inducedNorm p (moorePenrose A) < inducedNorm p X

end
end RegistryProblems.OP_00084
