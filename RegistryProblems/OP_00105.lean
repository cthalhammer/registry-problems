/-
  OP-00105: Lemos–Soares singular-value log-majorization

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00105

      theorem resolution : RegistryProblems.Problem_OP_00105 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-22/lean/NLA/MI22/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Copied Mat, spectralPower, weightedMean, leftProduct,
  singularValue, singularPrefix and SingularLogMajorized verbatim with their
  open line, left out WeightedLogMajorizationConjecture (its body is the body),
  operatorNorm, frobeniusSquared and the witness definitions, none of which the
  body uses, and dropped set_option autoImplicit false, the namespace and the
  noncomputable section lines.
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00105
noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The genuine real power from continuous functional calculus. It is never
replaced by entrywise powers or an assumed rational matrix certificate. -/
def spectralPower {n : ℕ} (A : Mat n) (t : ℝ) : Mat n := CFC.rpow A t

/-- The exact weighted mean, with the original noncommuting order of factors. -/
def weightedMean {n : ℕ} (A B : Mat n) (t : ℝ) : Mat n :=
  spectralPower A (1 / 2) *
    spectralPower (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)) t *
      spectralPower A (1 / 2)

def leftProduct {n : ℕ} (A B : Mat n) (t : ℝ) : Mat n :=
  spectralPower A t * weightedMean A B t * spectralPower B (1 - t)

/-- Mathlib's actual singular values of the linear map on complex Euclidean
space: descending, repeated with multiplicity, and zero beyond dimension n.
The index zero is the first singular value. No user-supplied list is involved. -/
def singularValue {n : ℕ} (A : Mat n) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues j

/-- The first k actual singular values, with the original one-based range
1,...,k represented as the zero-based range 0,...,k-1. -/
def singularPrefix {n : ℕ} (A : Mat n) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, singularValue A j

/-- Full log-majorization, including equality at n rather than weak
log-majorization. Both matrices have the same actual dimension n. -/
def SingularLogMajorized {n : ℕ} (X Y : Mat n) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k < n → singularPrefix X k ≤ singularPrefix Y k) ∧
    singularPrefix X n = singularPrefix Y n

/-- OP-00105: Lemos–Soares singular-value log-majorization -/
def _root_.RegistryProblems.Problem_OP_00105 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Mat n, A.PosDef → B.PosDef →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → SingularLogMajorized (leftProduct A B t) (A * B)

end
end RegistryProblems.OP_00105
