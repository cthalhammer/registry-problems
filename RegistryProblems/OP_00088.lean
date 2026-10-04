/-
  OP-00088: Number of components of a real interval eigenvalue set

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00088

      theorem resolution : RegistryProblems.Problem_OP_00088 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/intervals-and-absolute-value-equations/IV-06/lean/NLA/IV06/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions ComponentBoundConjecture uses are
  copied verbatim without their namespace and noncomputable-section lines;
  ComponentBoundConjecture itself becomes the body; left out as unused by it:
  characteristicDet and the dimension-three witness data (family, lower, upper,
  includedValue, includedA, includedB, includedVector, separator,
  determinantLower, determinantUpper).
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.Real

namespace RegistryProblems.OP_00088
noncomputable section

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Entrywise order, without imposing symmetry or coupling distinct entries. -/
def EntrywiseLE {n : ℕ} (L U : RealMatrix n) : Prop :=
  ∀ i j, L i j ≤ U i j

/-- The entire independent-entry closed interval family; fixed entries are allowed. -/
def InIntervalFamily {n : ℕ} (L U A : RealMatrix n) : Prop :=
  EntrywiseLE L A ∧ EntrywiseLE A U

/-- A real eigenvalue means an actual nonzero real eigenvector. -/
def HasRealEigenvalue {n : ℕ} (A : RealMatrix n) (lam : ℝ) : Prop :=
  ∃ v : Fin n → ℝ, v ≠ 0 ∧ A.mulVec v = lam • v

/-- The union of the real eigenvalues of every admissible matrix. -/
def realEigenvalueSet {n : ℕ} (L U : RealMatrix n) : Set ℝ :=
  {lam | ∃ A : RealMatrix n, InIntervalFamily L U A ∧ HasRealEigenvalue A lam}

/-- Cardinality is used, so infinite component spaces cannot count as zero. -/
def componentCard (S : Set ℝ) : Cardinal :=
  Cardinal.mk (ConnectedComponents S)

/-- OP-00088: Number of components of a real interval eigenvalue set -/
def _root_.RegistryProblems.Problem_OP_00088 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (L U : RealMatrix n),
    EntrywiseLE L U → componentCard (realEigenvalueSet L U) ≤ (n : Cardinal)

end
end RegistryProblems.OP_00088
