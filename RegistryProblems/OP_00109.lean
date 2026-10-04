/-
  OP-00109: Modulus-order determinant comparison with an arbitrary base power

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00109

      theorem resolution : RegistryProblems.Problem_OP_00109 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-29/lean/NLA/MI29/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the body of ModulusDeterminantConjecture
  copied verbatim; the witness definitions (witnessA, witnessM, witnessB) and
  the target def itself are left out, and set_option, namespace and
  noncomputable-section lines are dropped.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00109
noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder

/-- The actual unital continuous-functional-calculus power.
The explicit `CFC.rpow` avoids any pointwise function-power instance on matrices.
For a positive semidefinite matrix, exponent zero gives the identity matrix. -/
def spectralPower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    Matrix (Fin n) (Fin n) ℂ := CFC.rpow A r

/-- The actual matrix modulus, `CFC.sqrt (Xᴴ * X)`.
Mathlib's `CFC.abs` uses the positive square root from functional calculus. -/
def matrixModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := CFC.abs X

def leftMatrix {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k p : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  spectralPower A k + spectralPower (matrixModulus (A * B)) p

def rightMatrix {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k p : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  spectralPower A k + spectralPower (matrixModulus (B * A)) p

def leftDet {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k p : ℝ) : ℂ :=
  (leftMatrix A B k p).det

def rightDet {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k p : ℝ) : ℂ :=
  (rightMatrix A B k p).det

/-- OP-00109: Modulus-order determinant comparison with an arbitrary base power -/
def _root_.RegistryProblems.Problem_OP_00109 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    A.PosDef → B.IsHermitian → IsUnit B →
      ∀ k p : ℝ, 0 ≤ k → 0 ≤ p → rightDet A B k p ≤ leftDet A B k p

end
end RegistryProblems.OP_00109
