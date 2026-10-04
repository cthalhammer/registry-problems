/-
  OP-00101: The triangle conjecture for the maximal symmetric modulus

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00101

      theorem resolution : RegistryProblems.Problem_OP_00101 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-07/lean/NLA/MI07/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Copied matrixModulus, rootSequence, maximalModulus and
  unitaryConjugate verbatim with their open line, left out spectralNorm (with
  its open scoped Matrix.Norms.L2Operator in), TriangleConjecture (its body is
  the body) and the witness definitions, none of which the body uses, and
  dropped set_option autoImplicit false, the namespace and the noncomputable
  section lines.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup

namespace RegistryProblems.OP_00101
noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder Topology

/-- The actual positive modulus from continuous functional calculus. -/
def matrixModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := CFC.abs X

/-- The canonical sequence uses every positive integer exponent, indexed by `r+1`.
The outer exponent is a real CFC power, and the inner powers are matrix ring powers. -/
def rootSequence {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  CFC.rpow (matrixModulus X ^ (r + 1) +
    matrixModulus X.conjTranspose ^ (r + 1)) (((r + 1 : ℕ) : ℝ)⁻¹)

/-- Actual finite-dimensional limit of the canonical CFC sequence.
`limUnder` is totalized away from convergence. Every counterexample occurrence
has its convergence proved explicitly; its default value is never used. -/
def maximalModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := Filter.limUnder Filter.atTop (rootSequence X)

/-- Conjugation by an arbitrary genuine unitary matrix. -/
def unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (U : Matrix (Fin n) (Fin n) ℂ) * H *
    (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose

/-- OP-00101: The triangle conjecture for the maximal symmetric modulus -/
def _root_.RegistryProblems.Problem_OP_00101 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    ∃ U V : Matrix.unitaryGroup (Fin n) ℂ,
      maximalModulus (A + B) ≤
        unitaryConjugate U (maximalModulus A) + unitaryConjugate V (maximalModulus B)

end
end RegistryProblems.OP_00101
