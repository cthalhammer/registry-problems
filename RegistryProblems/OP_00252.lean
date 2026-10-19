/-
  OP-00252: The delta conjecture for minimum symmetric rank

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00252

      theorem resolution : RegistryProblems.Problem_OP_00252 := ...

  Formalised by OpenAI Codex AI agents, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/5487945e5a72abd952b0c89915915de8cc9b3e65/eigenvalues-and-inverse-problems/SP-11/lean/NLA/Statements/SP11.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. HasPattern and MinimumDegree are copied and the body
  is Target's body verbatim; the LeanCert import, the set_option lines and the
  #assert commands are dropped.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace RegistryProblems.OP_00252
noncomputable section

/-- Symmetry, the exact off-diagonal graph pattern, and unrestricted diagonal. -/
def HasPattern {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧
  ∀ i j, i ≠ j → (A i j ≠ 0 ↔ G.Adj i j)

/-- Classical decidability is used only to compute finite neighbor cardinalities. -/
noncomputable def MinimumDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact G.minDegree

/-- OP-00252: The delta conjecture for minimum symmetric rank -/
def _root_.RegistryProblems.Problem_OP_00252 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n),
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      HasPattern G A ∧ MinimumDegree G ≤ n - A.rank

end
end RegistryProblems.OP_00252
