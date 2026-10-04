/-
  OP-00108: Constant one in the logarithmic commutator inequality

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00108

      theorem resolution : RegistryProblems.Problem_OP_00108 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-27/lean/NLA/MI27/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The binder theorem logarithmic_commutator_bound (n,
  hn, A, B, hA, hB, htrace) is turned into a closed ∀-Prop with its statement
  copied verbatim; only Mat, trR, logM and traceNorm are kept from
  NLA/MI27/Definitions.lean (tracePos, opNorm, comm, entropy, relEntropy, E,
  flow, conjFlow, chi, h, StrictDensity and the kernel weights, used only by the
  other nineteen exports, are left out, and nothing from the reused NLA/MI24
  modules is needed); set_option, namespace and noncomputable-section lines are
  dropped; imports are the union of the Mathlib imports over the whole
  statement-side closure (Challenge, NLA/MI27/Definitions and the seven NLA/MI24
  modules it pulls in), and none is LeanCert.
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace RegistryProblems.OP_00108
noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Real part of the actual complex matrix trace, including for non-Hermitian products. -/
def trR {n : ℕ} (X : Mat n) : ℝ := (Matrix.trace X).re

/-- Natural spectral logarithm. Final entropy/logarithm applications are on PD matrices. -/
def logM {n : ℕ} (X : Mat n) : Mat n := CFC.log X

/-- The original full trace norm: trace of the positive square root of the Gram matrix. -/
def traceNorm {n : ℕ} (X : Mat n) : ℝ :=
  trR (CFC.rpow (Xᴴ * X) (1 / 2 : ℝ))

/-- OP-00108: Constant one in the logarithmic commutator inequality -/
def _root_.RegistryProblems.Problem_OP_00108 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (A B : Mat n), A.PosDef → B.PosDef → Matrix.trace (A + B) = 1 →
    traceNorm (B * logM (A + B) - logM (A + B) * B) ≤
      -(trR A) * Real.log (trR A) - (trR B) * Real.log (trR B)

end
end RegistryProblems.OP_00108
