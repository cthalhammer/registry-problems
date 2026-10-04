/-
  OP-00123: Random column subsets of arbitrary fixed-sparsity matrices

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00123

      theorem resolution : RegistryProblems.Problem_OP_00123 := ...

  Formalised by OpenAI Codex AI agents, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/randomized-and-low-rank-approximation/TR-07/lean/NLA/TR07/Definitions.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the body of SolvesTR07 (the type of
  random_column_subsets, which has no binders) copied verbatim; the target def
  itself and the module docstring are left out, the namespace and
  noncomputable-section lines are dropped, and the file's open Filter line is
  kept for Tendsto, atTop and nhds.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.Instances.Real.Lemmas

namespace RegistryProblems.OP_00123
noncomputable section

open scoped BigOperators
open Filter

abbrev Mat (k n : ℕ) := Matrix (Fin k) (Fin n) ℝ
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Exactly s nonzero signed entries in every column. -/
def SignedSparse {k n : ℕ} (s : ℕ) (M : Mat k n) : Prop := by
  classical
  exact (∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1) ∧
    ∀ j, (Finset.univ.filter fun i => M i j ≠ 0).card = s

/-- The actual selected rectangular matrix acting on its column coordinates. -/
def selectedAction {k n : ℕ} (M : Mat k n) (I : Finset (Fin n))
    (x : EuclideanSpace ℝ I) : Vec k :=
  WithLp.toLp 2 fun i => ∑ j : I, M i j * x j

/-- Infimum of the selected matrix's norm over its entire Euclidean unit sphere.
Lean's real infimum convention gives zero for the empty unit sphere; the
aspect-ratio hypothesis forces positive sample size eventually, so this
finite-prefix convention has no effect on the asserted limit. -/
def smallestSingular {k n : ℕ} (M : Mat k n) (I : Finset (Fin n)) : ℝ :=
  sInf {y : ℝ | ∃ x : EuclideanSpace ℝ I, ‖x‖ = 1 ∧ y = ‖selectedAction M I x‖}

/-- Probability of the strict tail event under uniform sampling without replacement. -/
def subsetTail {k n : ℕ} (M : Mat k n) (r : ℕ) (η : ℝ) : ℝ := by
  classical
  let samples := (Finset.univ : Finset (Fin n)).powersetCard r
  exact ((samples.filter fun I => η < smallestSingular M I).card : ℝ) / samples.card

/-- OP-00123: Random column subsets of arbitrary fixed-sparsity matrices -/
def _root_.RegistryProblems.Problem_OP_00123 : Prop :=
  ∀ (s : ℕ), 2 ≤ s → ∀ (C : ℝ), 1 ≤ C →
  ∀ (r n : ℕ → ℕ), (∀ k, r k ≤ k) → (∀ k, r k ≤ n k) →
    Tendsto (fun k : ℕ => (k : ℝ) / (r k : ℝ)) atTop (nhds C) →
    Tendsto (fun k : ℕ => (n k : ℝ) / (r k : ℝ)) atTop atTop →
    ∀ (M : (k : ℕ) → Mat k (n k)), (∀ᶠ k in atTop, SignedSparse s (M k)) →
    ∀ (η : ℝ), 0 < η →
      Tendsto (fun k => subsetTail (M k) (r k) η) atTop (nhds 0)

end
end RegistryProblems.OP_00123
