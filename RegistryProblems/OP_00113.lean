/-
  OP-00113: Connectedness of minimal positive semidefinite factorization orbits

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00113

      theorem resolution : RegistryProblems.Problem_OP_00113 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/nonnegative-and-positive-factorizations/PF-02/lean/NLA/PF02/Definitions.lean

  Copyright (c) 2026 George Stepaniants.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions AllMinimalOrbitsConnected uses are
  copied verbatim without their namespace and noncomputable-section lines;
  AllMinimalOrbitsConnected itself becomes the body; left out as unused by it:
  coord, rowCoordinates, orientationDet and the witness data (witnessM,
  witnessFactors, witnessTuple).
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order

namespace RegistryProblems.OP_00113
noncomputable section

open Matrix

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev FactorTuple (p q k : ℕ) := (Fin p → Mat k k) × (Fin q → Mat k k)

/-- Every row and column factor is genuinely real positive semidefinite. -/
def IsFactorization {p q k : ℕ} (M : Mat p q) (F : FactorTuple p q k) : Prop :=
  (∀ i, (F.1 i).PosSemidef) ∧ (∀ j, (F.2 j).PosSemidef) ∧
    ∀ i j, Matrix.trace (F.1 i * F.2 j) = M i j

/-- The full factorization space with its inherited finite-dimensional Euclidean topology. -/
abbrev Factorization {p q : ℕ} (M : Mat p q) (k : ℕ) :=
  {F : FactorTuple p q k // IsFactorization M F}

/-- The actual minimum among all positive integer factor sizes, including attainment. -/
def IsPSDRank {p q : ℕ} (M : Mat p q) (k : ℕ) : Prop :=
  IsLeast {ℓ : ℕ | 1 ≤ ℓ ∧ Nonempty (Factorization M ℓ)} k

/-- A single genuine invertible change of basis, on all row and column factors. -/
def Congruent {p q k : ℕ} {M : Mat p q} (F G : Factorization M k) : Prop :=
  ∃ S : (Mat k k)ˣ,
    (∀ i, G.val.1 i = (↑S : Mat k k).transpose * F.val.1 i * ↑S) ∧
    (∀ j, G.val.2 j = (↑(S⁻¹) : Mat k k) * F.val.2 j * (↑(S⁻¹) : Mat k k).transpose)

/-- Quotient topology on actual congruence orbits; the public orbit theorem checks exact equality. -/
abbrev OrbitSpace {p q : ℕ} (M : Mat p q) (k : ℕ) :=
  Quot (@Congruent p q k M)

/-- OP-00113: Connectedness of minimal positive semidefinite factorization orbits -/
def _root_.RegistryProblems.Problem_OP_00113 : Prop :=
  ∀ (k p q : ℕ), 3 ≤ k → 1 ≤ p → 1 ≤ q → ∀ M : Mat p q,
    (∀ i j, 0 ≤ M i j) → M.rank = k * (k + 1) / 2 → IsPSDRank M k →
    IsConnected (Set.univ : Set (OrbitSpace M k))

end
end RegistryProblems.OP_00113
