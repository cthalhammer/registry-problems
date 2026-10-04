/-
  OP-00091: A pointwise Lipschitz lower bound for the joint spectral radius

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00091

      theorem resolution : RegistryProblems.Problem_OP_00091 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-functions-and-stability/MF-06/lean/NLA/MF07/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions the body uses (Square, spectralNorm,
  matrixProduct, WordIn, wordNorms, familyGrowth, rootGrowth,
  jointSpectralRadius from NLA/MF07/Definitions.lean; pointFamilyDistance,
  directedSpectralDistance, canonicalHausdorff from NLA/MF05/Definitions.lean)
  are copied into one namespace, dropping their `open NLA.MF07` line and every
  definition the body does not use (including all of NLA/MF06/Definitions.lean);
  the binder theorem canonical_pointwise_lower_lipschitz, whose d is an implicit
  binder, is turned into a closed Prop with an explicit `∀ (d : ℕ)`.
-/

import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.UniformSpace.Dini

namespace RegistryProblems.OP_00091
noncomputable section

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Actual complex Euclidean operator norm, with no default entrywise norm. -/
def spectralNorm {d : ℕ} (A : Square d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A‖

/-- Chronological order: later factors act on the left. -/
def matrixProduct {d : ℕ} (w : List (Square d)) : Square d := w.reverse.prod

def WordIn {d : ℕ} (M : Set (Square d)) (w : List (Square d)) : Prop :=
  ∀ A ∈ w, A ∈ M

/-- All words are retained, including repetitions and infinitely many possible
generators. This is not a finite-generator restriction. -/
def wordNorms {d : ℕ} (M : Set (Square d)) (n : ℕ) : Set ℝ :=
  {r | ∃ w : List (Square d), w.length = n ∧ WordIn M w ∧
    r = spectralNorm (matrixProduct w)}

def familyGrowth {d : ℕ} (M : Set (Square d)) (n : ℕ) : ℝ := sSup (wordNorms M n)

/-- The n=0 value is immaterial to the limit and excluded from the infimum. -/
def rootGrowth {d : ℕ} (M : Set (Square d)) (n : ℕ) : ℝ :=
  Real.rpow (familyGrowth M n) (1 / (n : ℝ))

/-- Fekete's infimum formula. Its radius-one equivalence with the canonical
root limit is mandatory; no radius is assigned by definition. -/
def jointSpectralRadius {d : ℕ} (M : Set (Square d)) : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = rootGrowth M n}

/-- The literal infimum in the canonical spectral Hausdorff formula.
Nonempty compact families are required by all correspondence contracts. -/
def pointFamilyDistance {d : ℕ} (A : Square d) (N : Set (Square d)) : ℝ :=
  sInf ((fun B : Square d => spectralNorm (A - B)) '' N)

/-- The directed supremum in the canonical formula. -/
def directedSpectralDistance {d : ℕ} (M N : Set (Square d)) : ℝ :=
  sSup ((fun A : Square d => pointFamilyDistance A N) '' M)

/-- The original max-of-two-sup-inf formula, with the actual spectral norm. -/
def canonicalHausdorff {d : ℕ} (M N : Set (Square d)) : ℝ :=
  max (directedSpectralDistance M N) (directedSpectralDistance N M)

/-- OP-00091: A pointwise Lipschitz lower bound for the joint spectral radius -/
def _root_.RegistryProblems.Problem_OP_00091 : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (M : Set (Square d)), IsCompact M → M.Nonempty →
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : Set (Square d), IsCompact N → N.Nonempty →
        canonicalHausdorff M N < r →
        jointSpectralRadius M - C * canonicalHausdorff M N ≤ jointSpectralRadius N

end
end RegistryProblems.OP_00091
