/-
  OP-00119: The smallest-multiplier rule for nearest unit-absolute-determinant matrices

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00119

      theorem resolution : RegistryProblems.Problem_OP_00119 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/eigenvalues-and-inverse-problems/SP-04/lean/NLA/SP04/Definitions.lean

  Copyright (c) 2026 George Stepaniants.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions AllGenericSelectionRules uses are
  copied verbatim without their namespace and noncomputable-section lines;
  AllGenericSelectionRules itself becomes the body; left out as unused by it:
  Orthogonal, HasSVD, Admissible and the dimension-three witness data
  (largeRoot, positiveRoot, negativeMagnitude, selected/improved entries and
  matrices, sample data, endpoints, gramPolynomialValue, counterexampleFamily,
  SelectionFails).
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00119
noncomputable section

open scoped BigOperators Matrix

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Both determinant signs, exactly as in the canonical problem. -/
def Feasible {n : ℕ} (X : Mat n) : Prop := |X.det| = 1

/-- The actual sum-of-squares Frobenius norm, with its nonnegative square root. -/
def frobeniusSq {n : ℕ} (X : Mat n) : ℝ := ∑ i, ∑ j, (X i j) ^ 2

def frobeniusNorm {n : ℕ} (X : Mat n) : ℝ := Real.sqrt (frobeniusSq X)

/-- Every real stationary matrix and its real multiplier, without diagonal restrictions. -/
def Stationary {n : ℕ} (U X : Mat n) (c : ℝ) : Prop :=
  Feasible X ∧ Xᵀ * (U - X) = c • (1 : Mat n)

def stationaryPairs {n : ℕ} (U : Mat n) : Set (Mat n × ℝ) :=
  {p | Stationary U p.1 p.2}

/-- Unique minimizing pair, compared with the entire real stationary set. -/
def UniqueLeastStationary {n : ℕ} (U X : Mat n) (c : ℝ) : Prop :=
  Stationary U X c ∧ ∀ Y d, Stationary U Y d →
    |c| ≤ |d| ∧ (|c| = |d| → Y = X ∧ d = c)

/-- Actual global nearestness, including attainment at the displayed feasible matrix. -/
def IsNearest {n : ℕ} (U X : Mat n) : Prop :=
  Feasible X ∧ ∀ Y, Feasible Y → frobeniusNorm (U - X) ≤ frobeniusNorm (U - Y)

/-- Invertibility and distinct squared singular values: the real Gram polynomial has no repeated roots. -/
def RegularData {n : ℕ} (U : Mat n) : Prop :=
  U.det ≠ 0 ∧ (Uᵀ * U).charpoly.roots.Nodup

/-- The complete selection claim outside one arbitrary proper real algebraic exception.
The finite and regular premises retain the stated generic domain. -/
def GenericSelectionRule (n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n × Fin n) ℝ, p ≠ 0 ∧
    ∀ U : Mat n, MvPolynomial.eval (fun ij => U ij.1 ij.2) p ≠ 0 →
      RegularData U → (stationaryPairs U).Finite →
      ∀ X c, UniqueLeastStationary U X c → IsNearest U X

/-- OP-00119: The smallest-multiplier rule for nearest unit-absolute-determinant matrices -/
def _root_.RegistryProblems.Problem_OP_00119 : Prop :=
  ∀ n : ℕ, 2 ≤ n → GenericSelectionRule n

end
end RegistryProblems.OP_00119
