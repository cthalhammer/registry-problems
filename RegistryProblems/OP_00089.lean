/-
  OP-00089: Strict interlacing across block Lanczos iterations

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00089

      theorem resolution : RegistryProblems.Problem_OP_00089 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/eigenvalues-and-inverse-problems/KE-04/lean/NLA/KE04/Definitions.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions BlockLanczosConjecture uses are copied
  verbatim without their namespace and noncomputable-section lines;
  BlockLanczosConjecture itself becomes the body; left out as unused by it: act,
  krylovCombination, frameProjection, orderedEigenbasis, monicQuadratic,
  quadraticMatrix, compressedQuadratic, form and FullPrefixBlockLanczosClaim
  (the stronger full-prefix variant proved on the way).
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace RegistryProblems.OP_00089
noncomputable section

open scoped BigOperators

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Rect (n m : ℕ) := Matrix (Fin n) (Fin m) ℝ
abbrev Mat (n : ℕ) := Rect n n

def column {n m : ℕ} (M : Rect n m) (j : Fin m) : Vec n :=
  WithLp.toLp 2 (fun i => M i j)

def columnSpace {n m : ℕ} (M : Rect n m) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ (Set.range (column M))

def FullColumnRank {n p : ℕ} (V : Rect n p) : Prop :=
  LinearIndependent ℝ (column V)

/-- Degree is the first index; the second index selects a starting-block column. -/
def krylovColumns {n p : ℕ} (A : Mat n) (V : Rect n p) (ell : ℕ) :
    Fin ell × Fin p → Vec n :=
  fun rc => column (A ^ rc.1.val * V) rc.2

/-- Exactly the span of the columns of [V, A V, ..., A^(ell-1) V]. -/
def krylov {n p : ℕ} (A : Mat n) (V : Rect n p) (ell : ℕ) :
    Submodule ℝ (Vec n) :=
  Submodule.span ℝ (Set.range (krylovColumns A V ell))

/-- Actual dimension, with no eigenvalue or polynomial condition attached. -/
def FullBlockDimension {n p : ℕ} (A : Mat n) (V : Rect n p) (ell : ℕ) : Prop :=
  Module.finrank ℝ (krylov A V ell) = ell * p

/-- The canonical maximality convention. For p=0 there is no largest such index. -/
def LastFullBlockIteration {n p : ℕ} (A : Mat n) (V : Rect n p) (s : ℕ) : Prop :=
  FullBlockDimension A V s ∧ ∀ t, FullBlockDimension A V t → t ≤ s

/-- Arbitrary orthonormal columns spanning the exact Krylov space.
No compatibility or block-tridiagonal premise is imposed between iterations. -/
def IsKrylovBasis {n p : ℕ} (A : Mat n) (V : Rect n p) (ell : ℕ)
    (Q : Rect n (ell * p)) : Prop :=
  Q.transpose * Q = 1 ∧ columnSpace Q = krylov A V ell

/-- Over the real field this is exactly Q.transpose * A * Q. -/
def compression {n m : ℕ} (A : Mat n) (Q : Rect n m) : Mat m :=
  Q.conjTranspose * A * Q

/-- Mathlib sorts self-adjoint eigenvalues in decreasing order; `Fin.rev`
reverses that order. The genuine spectral theorem retains all multiplicities. -/
def orderedEigenvalues {m : ℕ} (M : Mat m) (hM : M.IsHermitian) : Fin m → ℝ :=
  fun r => (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM).eigenvalues
    finrank_euclideanSpace_fin r.rev

/-- Total zero-based indexing. The target's index bounds guarantee the first
branch; a separate index contract makes that fact explicit. -/
def eigenvalueAt {m : ℕ} (M : Mat m) (hM : M.IsHermitian) (i : ℕ) : ℝ :=
  if h : i < m then orderedEigenvalues M hM ⟨i, h⟩ else 0

/-- Only real symmetry is required to obtain the genuine compression spectrum.
The imported elementary Hermitian-congruence lemma supplies its symmetry. -/
def ritzValues {n m : ℕ} (A : Mat n) (hA : A.IsHermitian) (Q : Rect n m) :
    Fin m → ℝ :=
  orderedEigenvalues (compression A Q) (Matrix.isHermitian_conjTranspose_mul_mul Q hA)

def ritzValueAt {n m : ℕ} (A : Mat n) (hA : A.IsHermitian)
    (Q : Rect n m) (i : ℕ) : ℝ :=
  eigenvalueAt (compression A Q) (Matrix.isHermitian_conjTranspose_mul_mul Q hA) i

/-- The complete occupancy assertion through s, for all permitted k,j,i and
independently chosen orthonormal bases. The natural i is one-based as in the source. -/
def IterationOccupancy {n p : ℕ} (A : Mat n) (hA : A.IsHermitian)
    (V : Rect n p) (s : ℕ) : Prop :=
  ∀ k j : ℕ, 1 ≤ k → k < j → j ≤ s →
    ∀ (Qk : Rect n (k * p)) (Qj : Rect n (j * p)),
      IsKrylovBasis A V k Qk → IsKrylovBasis A V j Qj →
      ∀ i : ℕ, 1 ≤ i → i ≤ (k - 1) * p →
        ∃ r : Fin (j * p),
          ritzValueAt A hA Qk (i - 1) < ritzValues A hA Qj r ∧
          ritzValues A hA Qj r < ritzValueAt A hA Qk (i + p - 1)

/-- OP-00089: Strict interlacing across block Lanczos iterations -/
def _root_.RegistryProblems.Problem_OP_00089 : Prop :=
  ∀ (n p : ℕ) (A : Mat n) (hA : A.IsHermitian) (V : Rect n p),
    FullColumnRank V → ∀ s, LastFullBlockIteration A V s → IterationOccupancy A hA V s

end
end RegistryProblems.OP_00089
