/-
  OP-00093: Realizing arbitrary polynomial growth exponents by finite matrix families

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00093

      theorem resolution : RegistryProblems.Problem_OP_00093 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-functions-and-stability/MF-12/lean/NLA/MF12/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Only Square, spectralNorm, matrixProduct, wordNorms
  and familyGrowth are copied (with the file's `open scoped BigOperators
  Classical`), leaving out EuclideanVector and all construction-specific
  definitions; the Challenge's `open Filter` and `open scoped Topology`, which
  the body's Tendsto/atTop/𝓝 need, are appended at the end of the preamble; the
  binder theorem realizes_every_nonnegative_exponent is turned into a closed
  Prop.
-/

import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic

namespace RegistryProblems.OP_00093
noncomputable section

open scoped BigOperators Classical

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The genuine induced Euclidean operator norm, not an entrywise matrix norm. -/
def spectralNorm {d : ℕ} (A : Square d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖

/-- Chronological convention: later factors act on the left. -/
def matrixProduct {d : ℕ} (w : List (Square d)) : Square d := w.reverse.prod

/-- All genuine length-n family products. Repeated factors are unrestricted. -/
def wordNorms {d : ℕ} (M : Finset (Square d)) (n : ℕ) : Set ℝ :=
  {r | ∃ w : List (Square d), w.length = n ∧
    (∀ A ∈ w, A ∈ M) ∧ r = spectralNorm (matrixProduct w)}

/-- The finite maximum is a separate exported attainment obligation. -/
def familyGrowth {d : ℕ} (M : Finset (Square d)) (n : ℕ) : ℝ := sSup (wordNorms M n)

open Filter
open scoped Topology

/-- OP-00093: Realizing arbitrary polynomial growth exponents by finite matrix families -/
def _root_.RegistryProblems.Problem_OP_00093 : Prop :=
  ∀ (γ : ℝ), 0 ≤ γ →
    ∃ d : ℕ, 1 ≤ d ∧ ∃ M : Finset (Square d), M.Nonempty ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        (∀ n : ℕ, 1 ≤ n →
          c * Real.rpow (n : ℝ) γ ≤ familyGrowth M n ∧
          familyGrowth M n ≤ C * Real.rpow (n : ℝ) γ) ∧
        Tendsto (fun n : ℕ => Real.rpow (familyGrowth M n) (1 / (n : ℝ))) atTop (𝓝 1)

end
end RegistryProblems.OP_00093
