/-
  OP-00082: The exact four-step amplification of restarted Anderson acceleration

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00082

      theorem resolution : RegistryProblems.Problem_OP_00082 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/linear-systems-and-elimination/IE-18/lean/NLA/IE18/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Keeps the 10 definitions FourStepConjecture uses;
  leaves out pairValue (unused: pairListMaximum squares pairQuotient itself) and
  the witness data; the body is the body of def FourStepConjecture, verbatim;
  set_option autoImplicit false and the namespace/section lines are dropped.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace RegistryProblems.OP_00082
noncomputable section

open scoped BigOperators NNReal Classical

/-- The sum of coordinate squares, rather than the default norm on a Pi type. -/
def squaredNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i : Fin n, v i ^ 2

/-- The actual Euclidean norm of a real coordinate vector. -/
def euclideanNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (squaredNorm v)

/-- The scalar coefficient in the canonical residual map, using `A=I-M`.
At zero it is totalized by real division; `residualMap` handles zero explicitly. -/
def residualCoefficient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : ℝ :=
  dotProduct v ((1 - M).mulVec v) / squaredNorm ((1 - M).mulVec v)

/-- Two original Anderson steps. The canonical map explicitly sends zero to zero. -/
def residualMap {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  if v = 0 then 0
  else M.mulVec (v - residualCoefficient M v • (1 - M).mulVec v)

/-- Four original Anderson steps, namely two applications of the residual map. -/
def fourStepResidual {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ := residualMap M (residualMap M v)

/-- The unsquared Euclidean norm amplification appearing in IE-18. -/
def amplification {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : ℝ :=
  euclideanNorm (fourStepResidual M v) / euclideanNorm v

/-- Actual amplifications at every nonzero vector, with no default maximum. -/
def amplificationSet {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {r | ∃ v : Fin n → ℝ, v ≠ 0 ∧ r = amplification M v}

/-- The pairwise quotient. Real division gives zero if the denominator is zero,
which implements the canonical zero-denominator convention. -/
def pairQuotient (a b : ℝ) : ℝ :=
  a * b * (b - a) / (|a * (a - 1)| + |b * (b - 1)|)

/-- The maximum over distinct eigenvalue indices, retaining multiplicity.
The NNReal square equals the real square in `pairValue`; its finite supremum
is a true maximum for `n≥2`. The empty-index convention is outside that domain. -/
def pairListMaximum {n : ℕ} (μ : Fin n → ℝ) : ℝ :=
  (((Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2)).sup
    (fun ij => ‖pairQuotient (μ ij.1) (μ ij.2)‖₊ ^ 2) : ℝ≥0)

/-- The proposed factor using Mathlib's actual full eigenvalue list.
No user-supplied spectral certificate or diagonalization is assumed. -/
def pairMaximum {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) : ℝ := pairListMaximum hM.eigenvalues

/-- OP-00082: The exact four-step amplification of restarted Anderson acceleration -/
def _root_.RegistryProblems.Problem_OP_00082 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ M : Matrix (Fin n) (Fin n) ℝ, M ≠ 0 →
    ∀ hM : M.IsHermitian, (1 : ℝ) ∉ spectrum ℝ M →
      IsGreatest (amplificationSet M) (pairMaximum hM)

end
end RegistryProblems.OP_00082
