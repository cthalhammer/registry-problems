/-
  OP-00076: Counting real Hadamard matrices

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00076

      theorem resolution : RegistryProblems.Problem_OP_00076 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/frames-and-matrix-designs/FR-12/lean/NLA/FR12/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the body of CountingConjecture copied
  verbatim; doublingMatrix and doublingMap (used only by the construction
  exports) and the target def itself are left out, and set_option, namespace and
  noncomputable-section lines are dropped.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

namespace RegistryProblems.OP_00076
noncomputable section

open scoped BigOperators

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Exactly the canonical labeled real sign matrices and one-sided Gram identity.
There is no quotient by row/column permutations or signs. -/
def IsRealHadamard {n : ℕ} (A : Mat n) : Prop :=
  (∀ i j, A i j = 1 ∨ A i j = -1) ∧
    A * A.transpose = (n : ℝ) • (1 : Mat n)

/-- Individual matrices, with their original row and column labels. -/
def HadamardMatrices (n : ℕ) := {A : Mat n // IsRealHadamard A}

/-- The exact finite count. Finiteness of the displayed matrix subtype is a
required theorem, so `Nat.card` is not used to hide an infinite set. -/
def hadamardCount (n : ℕ) : ℕ := Nat.card (HadamardMatrices n)

/-- OP-00076: Counting real Hadamard matrices -/
def _root_.RegistryProblems.Problem_OP_00076 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → 4 ∣ n →
    (hadamardCount n : ℝ) ≤
      (2 : ℝ) ^ (C * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2))

end
end RegistryProblems.OP_00076
