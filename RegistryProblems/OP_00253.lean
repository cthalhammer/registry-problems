/-
  OP-00253: A chromatic lower bound for positive-semidefinite nullity with SAP

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00253

      theorem resolution : RegistryProblems.Problem_OP_00253 := ...

  Formalised by OpenAI Codex AI agents, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/099805ef1ce7347d373e47cccc3b2d7cf580a99e/eigenvalues-and-inverse-problems/SP-12/lean/NLA/Statements/SP12.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions are copied with their doc comments
  edited, and the body is Target's body verbatim; the LeanCert and
  Infrastructure imports, the set_option lines and the #assert commands are
  dropped.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace RegistryProblems.OP_00253
noncomputable section

open scoped BigOperators

/-- Symmetry, the exact off-diagonal graph pattern, and unrestricted diagonal. -/
def HasPattern {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧
  ∀ i j, i ≠ j → (A i j ≠ 0 ↔ G.Adj i j)

/-- The nonnegative real quadratic form; symmetry is in `HasPattern`. -/
def NonnegativeQuadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x i * A i j * x j

/-- The strong Arnold property: the only symmetric X with AX = 0, A ∘ X = 0
and zero diagonal is X = 0. -/
def StrongArnold {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, X i j = X j i) →
    A * X = 0 → (∀ i j, A i j * X i j = 0) →
    (∀ i, X i i = 0) → X = 0

/-- The least number of colors in a proper coloring; the set contains n. -/
noncomputable def ChromaticNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {c : ℕ | ∃ f : Fin n → Fin c, ∀ i j, G.Adj i j → f i ≠ f j}

/-- OP-00253: A chromatic lower bound for positive-semidefinite nullity with SAP -/
def _root_.RegistryProblems.Problem_OP_00253 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n),
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      HasPattern G A ∧ NonnegativeQuadraticForm A ∧ StrongArnold A ∧
      ChromaticNumber G - 1 ≤ n - A.rank

end
end RegistryProblems.OP_00253
