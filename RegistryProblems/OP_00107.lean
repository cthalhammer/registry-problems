/-
  OP-00107: Concave unitary-orbit subadditivity without monotonicity

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00107

      theorem resolution : RegistryProblems.Problem_OP_00107 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-26/lean/NLA/MI26/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Copied AdmissibleFunction, functionalCalculus and
  unitaryConjugate verbatim with their open line, left out
  SubadditivityConjecture (its body is the body) and the witness definitions
  (witnessFunction, witnessP, witnessQ, witnessImage, witnessVector), and
  dropped set_option autoImplicit false, the namespace and the noncomputable
  section lines.
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup

namespace RegistryProblems.OP_00107
noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder

/-- Exactly the canonical real-valued concave function class on the nonnegative
half-line. Values at negative arguments are unrestricted and are irrelevant for
positive semidefinite inputs. No continuity, monotonicity, or global
nonnegativity assumption is added. -/
def AdmissibleFunction (f : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ (Set.Ici 0) f ∧ 0 ≤ f 0

/-- Genuine real continuous functional calculus in the complex matrix algebra.
Every function is continuous on a Hermitian matrix's finite spectrum, even
when it is not continuous at an endpoint of the entire half-line. -/
def functionalCalculus {n : ℕ} (f : ℝ → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cfc (R := ℝ) f A

/-- Conjugation by an arbitrary complex unitary, with its actual conjugate transpose. -/
def unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (U : Matrix (Fin n) (Fin n) ℂ) * H *
    (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose

/-- OP-00107: Concave unitary-orbit subadditivity without monotonicity -/
def _root_.RegistryProblems.Problem_OP_00107 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    A.PosSemidef → B.PosSemidef → ∀ f : ℝ → ℝ, AdmissibleFunction f →
      ∃ U V : Matrix.unitaryGroup (Fin n) ℂ,
        functionalCalculus f (A + B) ≤
          unitaryConjugate U (functionalCalculus f A) +
            unitaryConjugate V (functionalCalculus f B)

end
end RegistryProblems.OP_00107
