/-
  OP-00077: Is the ideal GMRES bound sharp for every Jordan block?

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00077

      theorem resolution : RegistryProblems.Problem_OP_00077 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/linear-systems-and-elimination/IE-02/lean/NLA/IE02/Definitions.lean

  Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Keeps only the 15 definitions the target uses (the
  Toeplitz, Schur, Fourier, descent and affine-minimax machinery, lowerJordan,
  reversal and jordanDirections are left out); the binder theorem
  canonical_jordan_minimax (n k : ℕ) (lam : ℂ) (hn : 2 ≤ n) (hlam : lam ≠ 0) (hk
  : 1 ≤ k) (hkn : k < n) becomes a closed Prop with the same binder order and
  its conclusion copied verbatim from Challenge.lean; Challenge.lean's import
  LeanCert.Tactic and set_option leancert.trust are not needed by the statement
  and are dropped, as are set_option autoImplicit false and the
  namespace/section lines.
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Coprime.Basic

namespace RegistryProblems.OP_00077
noncomputable section

open scoped BigOperators Matrix
open Polynomial

abbrev Poly := Polynomial ℂ

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev H (n : ℕ) := EuclideanSpace ℂ (Fin n)

def DegreeLE (p : Poly) (m : ℕ) : Prop := p.degree ≤ (m : WithBot ℕ)

def euclideanLin {n : ℕ} (A : Square n) : H n →ₗ[ℂ] H n := Matrix.toEuclideanLin A

def euclideanCLM {n : ℕ} (A : Square n) : H n →L[ℂ] H n :=
  (euclideanLin A).toContinuousLinearMap

def operatorNorm {n : ℕ} (A : Square n) : ℝ := ‖euclideanCLM A‖

def unitSphere (n : ℕ) : Set (H n) := {x | ‖x‖ = 1}

def upperShift (n : ℕ) : Square n :=
  fun i j => if j.val = i.val + 1 then 1 else 0

def jordan (n : ℕ) (lam : ℂ) : Square n := lam • 1 + upperShift n

def polyEval {n : ℕ} (p : Poly) (A : Square n) : Square n := Polynomial.aeval A p

def Admissible (k : ℕ) (p : Poly) : Prop := DegreeLE p k ∧ p.eval 0 = 1

def gmresInner {n : ℕ} (A : Square n) (k : ℕ) (x : H n) : ℝ :=
  sInf {t : ℝ | ∃ p : Poly, Admissible k p ∧ t = ‖euclideanLin (polyEval p A) x‖}

def idealGMRES {n : ℕ} (A : Square n) (k : ℕ) : ℝ :=
  sInf {t : ℝ | ∃ p : Poly, Admissible k p ∧ t = operatorNorm (polyEval p A)}

def worstGMRES {n : ℕ} (A : Square n) (k : ℕ) : ℝ :=
  sSup (gmresInner A k '' unitSphere n)

/-- OP-00077: Is the ideal GMRES bound sharp for every Jordan block? -/
def _root_.RegistryProblems.Problem_OP_00077 : Prop :=
  ∀ (n k : ℕ) (lam : ℂ), 2 ≤ n → lam ≠ 0 → 1 ≤ k → k < n →
    worstGMRES (jordan n lam) k = idealGMRES (jordan n lam) k ∧
    (∀ x ∈ unitSphere n, ∃ p : Poly, Admissible k p ∧
      ‖euclideanLin (polyEval p (jordan n lam)) x‖ = gmresInner (jordan n lam) k x ∧
      ∀ q : Poly, Admissible k q → ‖euclideanLin (polyEval p (jordan n lam)) x‖ ≤
        ‖euclideanLin (polyEval q (jordan n lam)) x‖) ∧
    ∃ (p : Poly) (x : H n), Admissible k p ∧ x ∈ unitSphere n ∧
      operatorNorm (polyEval p (jordan n lam)) = idealGMRES (jordan n lam) k ∧
      ‖euclideanLin (polyEval p (jordan n lam)) x‖ = operatorNorm (polyEval p (jordan n lam)) ∧
      gmresInner (jordan n lam) k x = worstGMRES (jordan n lam) k ∧
      (∀ q : Poly, Admissible k q →
        operatorNorm (polyEval p (jordan n lam)) ≤ operatorNorm (polyEval q (jordan n lam))) ∧
      (∀ q : Poly, Admissible k q → ‖euclideanLin (polyEval p (jordan n lam)) x‖ ≤
        ‖euclideanLin (polyEval q (jordan n lam)) x‖) ∧
      (∀ z ∈ unitSphere n, gmresInner (jordan n lam) k z ≤ gmresInner (jordan n lam) k x)

end
end RegistryProblems.OP_00077
