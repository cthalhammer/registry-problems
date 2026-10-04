/-
  OP-00100: Thompson-type domination for the arithmetic symmetric modulus

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00100

      theorem resolution : RegistryProblems.Problem_OP_00100 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-06/lean/NLA/MI06/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Copied matrixModulus, symmetricModulus and
  unitaryConjugate verbatim with their open line, left out DominationConjecture
  (its body is the body) and the auxiliary and witness definitions
  (squaredLength, quadraticForm, rankOne, witnessA, witnessB, the modulus
  tables, directions and missingA/B) used only by other exports, and dropped
  set_option autoImplicit false, the namespace and the noncomputable section
  lines.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup

namespace RegistryProblems.OP_00100
noncomputable section

open scoped BigOperators Classical ComplexOrder Matrix MatrixOrder

/-- The genuine positive modulus, defined by continuous functional calculus. -/
def matrixModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := CFC.abs X

/-- The arithmetic average of the right and left moduli. -/
def symmetricModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (matrixModulus X + matrixModulus X.conjTranspose)

/-- Conjugation by an arbitrary genuine complex unitary matrix. -/
def unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (U : Matrix (Fin n) (Fin n) ℂ) * H *
    (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose

/-- OP-00100: Thompson-type domination for the arithmetic symmetric modulus -/
def _root_.RegistryProblems.Problem_OP_00100 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    ∃ U V : Matrix.unitaryGroup (Fin n) ℂ,
      symmetricModulus (A + B) ≤
        (Real.sqrt 2 : ℂ) •
          (unitaryConjugate U (symmetricModulus A) +
            unitaryConjugate V (symmetricModulus B))

end
end RegistryProblems.OP_00100
