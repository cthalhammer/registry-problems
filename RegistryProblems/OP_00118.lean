/-
  OP-00118: Critical-point counts for symmetric rank-two approximation with diagonal zeros

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00118

      theorem resolution : RegistryProblems.Problem_OP_00118 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/randomized-and-low-rank-approximation/RA-20/lean/NLA/RA20/Definitions.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the body of criticalCountConjecture copied
  verbatim; the n = s = 3 witness definitions (hollow, ExactlyOneZero, ABCPoly,
  abcPolynomial, abcIdeal, ABCCoordinateRing, polynomialHollow,
  genericPolynomial, GenericData, candidate, planeCoordinates), the module
  docstring and the target def itself are left out, and the
  noncomputable-section, namespace and end lines are dropped.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Smooth.Locus

namespace RegistryProblems.OP_00118
noncomputable section

open scoped BigOperators

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Variables (n : ℕ) := Fin n × Fin n
abbrev Poly (n : ℕ) := MvPolynomial (Variables n) ℂ

def coordinates {n : ℕ} (X : Mat n) : Variables n → ℂ :=
  fun ij => X ij.1 ij.2

def matrixOfCoordinates {n : ℕ} (x : Variables n → ℂ) : Mat n :=
  fun i j => x (i, j)

/-- The actual symmetric rank-at-most-two variety, with the first `s` diagonal
entries zero. The canonical parameter range is imposed by the conjecture. -/
def variety (n s : ℕ) : Set (Mat n) :=
  {X | X.IsSymm ∧ X.rank ≤ 2 ∧ ∀ i : Fin n, i.val < s → X i i = 0}

def coordinateVariety (n s : ℕ) : Set (Variables n → ℂ) :=
  {x | matrixOfCoordinates x ∈ variety n s}

/-- Taking all polynomials vanishing on the actual point set gives its reduced
coordinate ring, independently of any proposed equations or chosen generators. -/
def definingIdeal (n s : ℕ) : Ideal (Poly n) :=
  MvPolynomial.vanishingIdeal ℂ (coordinateVariety n s)

abbrev CoordinateRing (n s : ℕ) := Poly n ⧸ definingIdeal n s

/-- A point is smooth precisely when its point prime in the reduced coordinate
ring lies in Mathlib's smooth locus over `ℂ`. The prime is specified by its
pullback, so no prime, chart, dimension or Jacobian-rank assumption is supplied. -/
def SmoothPoint (n s : ℕ) (X : Mat n) : Prop :=
  X ∈ variety n s ∧
    ∃ p : PrimeSpectrum (CoordinateRing n s),
      PrimeSpectrum.comap (Ideal.Quotient.mk (definingIdeal n s)) p =
        MvPolynomial.pointToPoint (coordinates X) ∧
      p ∈ Algebra.smoothLocus ℂ (CoordinateRing n s)

/-- The Zariski tangent directions annihilate the differentials of every
polynomial in the reduced defining ideal. -/
def TangentVector (n s : ℕ) (X Z : Mat n) : Prop :=
  ∀ p ∈ definingIdeal n s,
    (∑ ij : Variables n,
      MvPolynomial.eval (coordinates X) (MvPolynomial.pderiv ij p) *
        coordinates Z ij) = 0

/-- The complex bilinear extension of the full Frobenius squared distance.
On symmetric matrices, each off-diagonal term occurs twice. -/
def fullFrobeniusDistance {n : ℕ} (U X : Mat n) : ℂ :=
  ∑ i, ∑ j, (X i j - U i j) ^ 2

def SmoothCriticalPoint (n s : ℕ) (U X : Mat n) : Prop :=
  SmoothPoint n s X ∧
    ∀ Z : Mat n, TangentVector n s X Z →
      fderiv ℂ (fullFrobeniusDistance U) X Z = 0

def criticalSet (n s : ℕ) (U : Mat n) : Set (Mat n) :=
  {X | SmoothCriticalPoint n s U X}

/-- A cardinal equality, so an infinite critical set is never silently assigned
the finite count zero. -/
def HasCriticalCount (n s : ℕ) (U : Mat n) (m : ℕ) : Prop :=
  Cardinal.mk {X : Mat n // X ∈ criticalSet n s U} = (m : Cardinal)

/-- A genuine generic count: the exceptional polynomial need not be the one
used by the counterexample, and must not vanish identically on symmetric data.
Any nonempty Zariski-open set contains such a nonempty principal open set. -/
def HasGenericCriticalCount (n s m : ℕ) : Prop :=
  ∃ q : Poly n,
    (∃ U : Mat n, U.IsSymm ∧ MvPolynomial.eval (coordinates U) q ≠ 0) ∧
    ∀ U : Mat n, U.IsSymm → MvPolynomial.eval (coordinates U) q ≠ 0 →
      HasCriticalCount n s U m

def predictedCount (n s : ℕ) : ℕ :=
  if s = 1 then 3 * (n - 1) - 2
  else if s = 2 then 9 * (n - 2) - 2
  else if s = 3 then 27 * (n - 3) + 4
  else if s = 4 then 81 * (n - 4) + 28
  else 0

/-- OP-00118: Critical-point counts for symmetric rank-two approximation with diagonal zeros -/
def _root_.RegistryProblems.Problem_OP_00118 : Prop :=
  ∀ n s : ℕ, 3 ≤ n → 1 ≤ s → s ≤ 4 → s ≤ n →
    HasGenericCriticalCount n s (predictedCount n s)

end
end RegistryProblems.OP_00118
