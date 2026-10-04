/-
  OP-00080: A sharp subset bound for worst-case normal GMRES

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00080

      theorem resolution : RegistryProblems.Problem_OP_00080 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/linear-systems-and-elimination/IE-16/lean/NLA/IE16/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Keeps the 8 definitions IE16Conjecture uses, with
  their explanatory comments; leaves out the nine-point counterexample data
  (omega, epsilon, clusterPoint, explicitL, denominator, witnessPolynomial, the
  numeric bounds and ExplicitCertificate); the body is the body of def
  IE16Conjecture, verbatim; set_option autoImplicit false and the
  namespace/section lines are dropped.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Powerset

namespace RegistryProblems.OP_00080
noncomputable section

open scoped BigOperators Classical

abbrev Poly := Polynomial ℂ

/- The finite maximum is totalized at the empty set.  All occurrences in the
   canonical target have nonempty sets, since k >= 1 and |L| >= 3. -/
def maxModulus (L : Finset ℂ) (p : Poly) : ℝ :=
  if hL : L.Nonempty then L.sup' hL (fun z => ‖p.eval z‖) else 0

def feasible (L : Finset ℂ) (k : ℕ) (p : Poly) : Prop :=
  p.natDegree ≤ k ∧ p.eval 0 = 1

def feasibleValues (L : Finset ℂ) (k : ℕ) : Set ℝ :=
  {r | ∃ p : Poly, feasible L k p ∧ maxModulus L p = r}

/- This is exactly M_k(L), with the finite maximum above and the infimum over
   all complex polynomials of degree at most k normalized by p(0)=1. -/
def M (L : Finset ℂ) (k : ℕ) : ℝ := sInf (feasibleValues L k)

def subsetFamily (L : Finset ℂ) (k : ℕ) : Finset (Finset ℂ) :=
  L.powerset.filter (fun S => S.card = k + 1)

/- This is B_k(L) = max_{S subset L, |S|=k+1} M_k(S).  The empty-family
   branch is irrelevant under the canonical admissibility hypotheses. -/
def subsetMax (L : Finset ℂ) (k : ℕ) : ℝ :=
  if hS : (subsetFamily L k).Nonempty then
    (subsetFamily L k).sup' hS (fun S => M S k)
  else 0

def admissible (L : Finset ℂ) (n : ℕ) : Prop :=
  L.card = n ∧ ∀ z ∈ L, z ≠ 0

/-- OP-00080: A sharp subset bound for worst-case normal GMRES -/
def _root_.RegistryProblems.Problem_OP_00080 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ L : Finset ℂ, admissible L n →
    ∀ k : ℕ, 1 ≤ k → k ≤ n - 2 →
      M L k ≤ (4 / Real.pi) * subsetMax L k

end
end RegistryProblems.OP_00080
