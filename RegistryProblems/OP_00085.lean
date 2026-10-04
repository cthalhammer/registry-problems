/-
  OP-00085: Where a symmetric stochastic matrix can be spectrally unique

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00085

      theorem resolution : RegistryProblems.Problem_OP_00085 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/eigenvalues-and-inverse-problems/IS-02/lean/NLA/IS02/Definitions.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Keeps the 14 definitions targetNecessaryCondition
  uses; leaves out realEigenvalueMultiset (used only by the bridge export),
  counterexample and counterexampleClaim; the body is the body of def
  targetNecessaryCondition, verbatim; set_option autoImplicit false and the
  namespace/section lines are dropped.
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00085
noncomputable section

open scoped BigOperators

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def symmetric {n : ℕ} (A : Mat n) : Prop := ∀ i j, A i j = A j i

def entrywiseNonnegative {n : ℕ} (A : Mat n) : Prop := ∀ i j, 0 ≤ A i j

def stochastic {n : ℕ} (A : Mat n) : Prop :=
  ∀ i, (∑ j : Fin n, A i j) = 1

def symmetricStochastic (n : ℕ) : Set (Mat n) :=
  {A | symmetric A ∧ entrywiseNonnegative A ∧ stochastic A}

def trace {n : ℕ} (A : Mat n) : ℝ := ∑ i : Fin n, A i i

def permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Mat n) : Mat n :=
  fun i j => A (σ i) (σ j)

def permutationSimilar {n : ℕ} (A B : Mat n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), B = permute σ A

/-- For real symmetric matrices, characteristic-polynomial equality is the
exact finite-dimensional encoding of equality of eigenvalues with
multiplicities used by the source theorem. The explicit bridge contract below
must connect this encoding to the real root multiset. -/
def sameSpectrum {n : ℕ} (A B : Mat n) : Prop :=
  Matrix.charpoly A = Matrix.charpoly B

def spectrallyUnique {n : ℕ} (A : Mat n) : Prop :=
  ∀ B, B ∈ symmetricStochastic n → sameSpectrum A B → permutationSimilar A B

def segment {n : ℕ} (X Y : Mat n) : Set (Mat n) :=
  {Z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ Z = (1 - t) • X + t • Y}

def vertex (n : ℕ) (V : Mat n) : Prop :=
  V ∈ symmetricStochastic n ∧
    ∀ U W, U ∈ symmetricStochastic n → W ∈ symmetricStochastic n →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        V = (1 - t) • U + t • W → t = 0 ∨ t = 1 ∨ U = W

def flatMatrix (n : ℕ) : Mat n :=
  fun i j => if i = j then 0 else (1 : ℝ) / ((n - 1 : ℕ) : ℝ)

def assertedLocus (n : ℕ) : Set (Mat n) :=
  segment (1 : Mat n) (flatMatrix n) ∪
    {A | ∃ V, vertex n V ∧ (A ∈ segment (1 : Mat n) V ∨
      A ∈ segment (flatMatrix n) V)}

/-- OP-00085: Where a symmetric stochastic matrix can be spectrally unique -/
def _root_.RegistryProblems.Problem_OP_00085 : Prop :=
  ∀ n, 4 ≤ n → ∀ A : Mat n,
    A ∈ symmetricStochastic n → 0 < trace A →
    spectrallyUnique A → A ∈ assertedLocus n

end
end RegistryProblems.OP_00085
