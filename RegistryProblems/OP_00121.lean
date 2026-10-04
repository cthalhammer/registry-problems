/-
  OP-00121: A real-valued symbol on a Jordan curve and real Toeplitz spectra

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00121

      theorem resolution : RegistryProblems.Problem_OP_00121 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/eigenvalues-and-inverse-problems/SP-06/lean/NLA/SP06/Definitions.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The theorem is `¬ targetImplication`, so the body is
  targetImplication's body; only LaurentCoefficients, laurentEval,
  hasAdmissibleBand, toeplitz, hasRealJordanCurve and allFiniteSpectraReal are
  copied, leaving out the witness, auxiliary, radial-curve and
  counterexampleClaim definitions.
-/

import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00121
noncomputable section

/-- The coefficients of a finite complex Laurent polynomial. -/
abbrev LaurentCoefficients := ℤ →₀ ℂ

def laurentEval (b : LaurentCoefficients) (z : ℂ) : ℂ :=
  b.sum (fun k a => a * z ^ k)

/-- The original positive lower and upper bandwidths and nonzero extremes. -/
def hasAdmissibleBand (b : LaurentCoefficients) : Prop :=
  ∃ r s : ℕ, 1 ≤ r ∧ 1 ≤ s ∧
    (∀ k : ℤ, k < -(r : ℤ) ∨ (s : ℤ) < k → b k = 0) ∧
    b (-(r : ℤ)) * b (s : ℤ) ≠ 0

def toeplitz (b : LaurentCoefficients) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => b ((i.val : ℤ) - (j.val : ℤ))

/-- A genuine Jordan curve, as the continuous injective image of the unit
circle, avoiding zero and contained in the real locus of the symbol. -/
def hasRealJordanCurve (b : LaurentCoefficients) : Prop :=
  ∃ γ : Circle → ℂ, Continuous γ ∧ Function.Injective γ ∧
    (∀ u, γ u ≠ 0) ∧ (∀ u, (laurentEval b (γ u)).im = 0)

/-- The actual algebra spectrum of every positive finite Toeplitz section. -/
def allFiniteSpectraReal (b : LaurentCoefficients) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ z : ℂ, z ∈ spectrum ℂ (toeplitz b n) → z.im = 0

/-- OP-00121: A real-valued symbol on a Jordan curve and real Toeplitz spectra -/
def _root_.RegistryProblems.Problem_OP_00121 : Prop :=
  ∀ b : LaurentCoefficients,
    hasAdmissibleBand b → hasRealJordanCurve b → allFiniteSpectraReal b

end
end RegistryProblems.OP_00121
