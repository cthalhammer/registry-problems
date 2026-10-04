/-
  OP-00106: Corrected generalized geometric-mean product conjecture

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00106

      theorem resolution : RegistryProblems.Problem_OP_00106 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-23/lean/NLA/MI23/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Copied Mat, spectralPower, generalizedMean,
  orderedEigenvalues, LogMajorized, leftProduct and rightProduct verbatim with
  their open line, left out HasOrderedPositiveEigenvalues, largestEigenvalue,
  GeneralizedGeometricMeanConjecture (its body is the body), operatorNorm,
  frobeniusSquared, squaredGap and the witness definitions, none of which the
  body uses, and dropped set_option autoImplicit false, the namespace and the
  noncomputable section lines.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00106
noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The genuine continuous-functional-calculus real power. This is not
entrywise exponentiation or a rational proxy for spectral exponentiation. -/
def spectralPower {n : ℕ} (A : Mat n) (r : ℝ) : Mat n := CFC.rpow A r

/-- The generalized geometric mean, retaining the exact noncommuting factor order
and the independent real parameters `r` and `t` from the canonical target. -/
def generalizedMean {n : ℕ} (A B : Mat n) (r t : ℝ) : Mat n :=
  spectralPower A (r / 2) *
    spectralPower (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)) t *
      spectralPower A (r / 2)

/-- Actual characteristic-polynomial roots with algebraic multiplicity, mapped
to their real parts and sorted decreasingly. On products of positive definite
matrices the required semantic theorem proves every root is real and positive,
the list has exactly `n` entries, and no root or multiplicity is discarded.
No fallback Hermitian matrix or assumed numerical eigenvalue list is used. -/
def orderedEigenvalues {n : ℕ} (A : Mat n) : List ℝ :=
  (A.charpoly.roots.map Complex.re).sort (· ≥ ·)

/-- Log-majorization for equal-length lists: all proper nonempty prefix products
are bounded and the complete products are equal. Positivity and decreasing order
of every list arising in the conjecture are separate proved semantic obligations.
In particular, this is not weak log-majorization or only its first inequality. -/
def LogMajorized (a b : List ℝ) : Prop :=
  a.length = b.length ∧
    (∀ k : ℕ, 1 ≤ k → k < a.length → (a.take k).prod ≤ (b.take k).prod) ∧
    a.prod = b.prod

def leftProduct {n : ℕ} (A B : Mat n) (r s p t : ℝ) : Mat n :=
  spectralPower (generalizedMean A B r t) p *
    spectralPower (generalizedMean A B s (1 - t)) p

def rightProduct {n : ℕ} (A B : Mat n) (r s p : ℝ) : Mat n :=
  spectralPower A (p * (r + s - 1)) * spectralPower B p

/-- OP-00106: Corrected generalized geometric-mean product conjecture -/
def _root_.RegistryProblems.Problem_OP_00106 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Mat n, A.PosDef → B.PosDef →
    ∀ r s p t : ℝ, 1 ≤ p → 0 ≤ t → t ≤ 1 →
      ((1 ≤ r ∧ 1 ≤ s) ∨ (r ≤ 0 ∧ s ≤ 0)) →
        LogMajorized (orderedEigenvalues (leftProduct A B r s p t))
          (orderedEigenvalues (rightProduct A B r s p))

end
end RegistryProblems.OP_00106
