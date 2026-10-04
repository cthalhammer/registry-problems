/-
  OP-00117: Convexity of the expected error of volume-sampled column subsets

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00117

      theorem resolution : RegistryProblems.Problem_OP_00117 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/randomized-and-low-rank-approximation/RA-07/lean/NLA/RA07/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the body of ConvexityConjecture copied
  verbatim; the proof-support definitions (generatingPolynomial,
  iteratedGeneratingDerivative, powerSum, pairGap, certificateDenominator) and
  the target def itself are left out, and set_option, namespace and
  noncomputable-section lines are dropped.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

namespace RegistryProblems.OP_00117
noncomputable section

open scoped BigOperators Polynomial

/-- The actual canonical sum over all subsets of the indicated cardinality. -/
def elementarySymmetric {n : ℕ} (lam : Fin n → ℝ) (j : ℕ) : ℝ :=
  ((Finset.univ : Finset (Fin n)).powersetCard j).sum fun S => S.prod lam

/-- The exact sequence in RA-07, defined using ordinary real division. -/
def errorSequence {n : ℕ} (lam : Fin n → ℝ) (j : ℕ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) * elementarySymmetric lam (j + 1) / elementarySymmetric lam j

/-- OP-00117: Convexity of the expected error of volume-sampled column subsets -/
def _root_.RegistryProblems.Problem_OP_00117 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ lam : Fin n → ℝ, (∀ i, 0 < lam i) →
    ∀ j : ℕ, 2 ≤ j → j ≤ n - 1 →
      0 ≤ errorSequence lam (j - 1) - 2 * errorSequence lam j + errorSequence lam (j + 1)

end
end RegistryProblems.OP_00117
