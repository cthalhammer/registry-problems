/-
  OP-00103: A q-permanent inequality for subset-preserving permutations

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00103

      theorem resolution : RegistryProblems.Problem_OP_00103 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-19/lean/NLA/MI19/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Copied inversionCount, qPermanentTerm, qPermanent,
  PreservesSubset and restrictedQPermanent verbatim with their open line, left
  out SubsetConjecture (its body is the body) and the witness definitions
  (witness, gramFactor, witnessQ, witnessSubset), and dropped set_option
  autoImplicit false, the namespace and the noncomputable section lines.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace RegistryProblems.OP_00103
noncomputable section

open scoped BigOperators ComplexOrder

/-- The number of inversions in the full original ordering of `Fin n`.
The paper's index `i + 1` is represented by Lean index `i`. -/
def inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    fun ij => ij.1 < ij.2 ∧ σ ij.2 < σ ij.1).card

/-- The term of the complex `q`-permanent belonging to a permutation.
The natural power retains the convention `0 ^ 0 = 1`. -/
def qPermanentTerm {n : ℕ} (q : ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  (q : ℂ) ^ inversionCount σ * ∏ i : Fin n, A i (σ i)

/-- The `q`-permanent, with all inversions counted in the original ordering. -/
def qPermanent {n : ℕ} (q : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), qPermanentTerm q A σ

/-- Setwise preservation, not pointwise fixation and not an initial-segment test. -/
abbrev PreservesSubset {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Prop :=
  S.image σ = S

/-- The subset-preserving sum. The exponent still uses `inversionCount` on
all `n` positions; it is not a product of smaller `q`-permanents. -/
def restrictedQPermanent {n : ℕ} (q : ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    (S : Finset (Fin n)) : ℂ :=
  ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ => PreservesSubset σ S), qPermanentTerm q A σ

/-- OP-00103: A q-permanent inequality for subset-preserving permutations -/
def _root_.RegistryProblems.Problem_OP_00103 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef →
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ S : Finset (Fin n),
      S.Nonempty → S ≠ Finset.univ → restrictedQPermanent q A S ≤ qPermanent q A

end
end RegistryProblems.OP_00103
