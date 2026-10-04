/-
  OP-00114: Rational factors for rational completely positive boundary matrices

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00114

      theorem resolution : RegistryProblems.Problem_OP_00114 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/nonnegative-and-positive-factorizations/PF-03/lean/NLA/PF03/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions RationalBoundaryFactorability uses are
  copied verbatim without their set_option, noncomputable-section and namespace
  lines; RationalBoundaryFactorability itself becomes the body; left out as
  unused by it: castVector and everything after RationalBoundaryFactorability
  (the cube-root-of-2 seed, cone, Fourier-Motzkin and padding definitions), and
  the project module NLA.PF03.RawData is not imported (nothing in the body's
  closure uses it), its own Mathlib imports being kept in the list.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Instances.Matrix

namespace RegistryProblems.OP_00114
noncomputable section

open scoped BigOperators Classical Matrix

abbrev QMat (m n : ℕ) := Matrix (Fin m) (Fin n) ℚ
abbrev RMat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The actual symmetric-matrix subspace, with its inherited subtype topology. -/
abbrev SymMatrix (F : Type) (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) F // A.IsSymm}

def castMatrix {m n : ℕ} (A : QMat m n) : RMat m n :=
  A.map (fun q : ℚ => (q : ℝ))

/-- Only the already proved generic map-symmetry fact constructs the subtype. -/
def realCast {n : ℕ} (A : SymMatrix ℚ n) : SymMatrix ℝ n :=
  ⟨castMatrix A.val, A.property.map (fun q : ℚ => (q : ℝ))⟩

def CompletelyPositive {n : ℕ} (A : SymMatrix ℝ n) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ ∃ B : RMat n m,
    (∀ i j, 0 ≤ B i j) ∧ A.val = B * Bᵀ

def CPSet (n : ℕ) : Set (SymMatrix ℝ n) :=
  {A | CompletelyPositive A}

def RationalFactor {n : ℕ} (A : SymMatrix ℚ n) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ ∃ B : QMat n m,
    (∀ i j, 0 ≤ B i j) ∧ A.val = B * Bᵀ

/-- OP-00114: Rational factors for rational completely positive boundary matrices -/
def _root_.RegistryProblems.Problem_OP_00114 : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ A : SymMatrix ℚ n,
    realCast A ∈ frontier (CPSet n) → RationalFactor A

end
end RegistryProblems.OP_00114
