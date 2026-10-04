/-
  OP-00120: Symmetric minimizer for a positive definite Jordan–Kronecker product

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00120

      theorem resolution : RegistryProblems.Problem_OP_00120 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/eigenvalues-and-inverse-problems/SP-05/lean/NLA/SP05/Definitions.lean

  Copyright (c) 2026 George Stepaniants.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions the statement uses are copied verbatim
  without their namespace and noncomputable-section lines; the binder theorem
  canonical_result becomes the closed Prop ∀ (n : ℕ), 2 ≤ n → ∀ (A B : Mat n),
  A.PosDef → B.PosDef → ..., otherwise verbatim; left out as unused by it:
  columnVec, frobeniusSq, jordanMatrix and skewExample.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Vec

namespace RegistryProblems.OP_00120
noncomputable section

open scoped BigOperators Matrix

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vec (n : ℕ) := (Fin n × Fin n) → ℝ
abbrev Operator (n : ℕ) := Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ

/-- The actual commutation permutation matrix, swapping row and column indices. -/
def commutationMatrix (n : ℕ) : Operator n :=
  fun i j => if i = j.swap then 1 else 0

/-- Literal real Rayleigh quotient; target vectors are always nonzero. -/
def rayleigh {n : ℕ} (K : Operator n) (v : Vec n) : ℝ :=
  dotProduct v (K *ᵥ v) / dotProduct v v

/-- All quotient values in the specified eigenspace of the actual commutation matrix. -/
def sectorValues {n : ℕ} (A B : Mat n) (ε : ℝ) : Set ℝ :=
  {r | ∃ v : Vec n, v ≠ 0 ∧ commutationMatrix n *ᵥ v = ε • v ∧
    r = rayleigh (Matrix.kronecker A B) v}

/-- OP-00120: Symmetric minimizer for a positive definite Jordan–Kronecker product -/
def _root_.RegistryProblems.Problem_OP_00120 : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (A B : Mat n), A.PosDef → B.PosDef →
    ∃ a b : ℝ, IsLeast (sectorValues A B 1) a ∧
      IsLeast (sectorValues A B (-1)) b ∧ a ≤ b

end
end RegistryProblems.OP_00120
