/-
  OP-00211: Comon's exact-rank conjecture for Hankel tensors

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00211

      theorem resolution : RegistryProblems.Problem_OP_00211 := ...

  Formalised by OpenAI Codex AI agents, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/099805ef1ce7347d373e47cccc3b2d7cf580a99e/tensor-computations/TR-14/lean/NLA/Statements/TR14.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions are copied with their doc comments
  edited, and the body is Target's body verbatim; the LeanCert and
  Infrastructure imports, the set_option lines and the #assert commands are
  dropped.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace RegistryProblems.OP_00211
noncomputable section

open scoped BigOperators

/-- Zero-based sum of tensor indices, with its exact finite bound. -/
def HankelIndex {m n : ℕ} (i : Fin m → Fin n) : Fin (m * (n - 1) + 1) :=
  ⟨∑ k, (i k).val, by
    calc
      (∑ k, (i k).val) ≤ ∑ _k : Fin m, (n - 1) :=
        Finset.sum_le_sum fun k _ => by have := (i k).isLt; omega
      _ = m * (n - 1) := by simp
      _ < m * (n - 1) + 1 := Nat.lt_succ_self _⟩

def Hankel {m n : ℕ} (h : Fin (m * (n - 1) + 1) → ℂ)
    (i : Fin m → Fin n) : ℂ :=
  h (HankelIndex i)

/-- A sum of r terms u₁ ⊗ ⋯ ⊗ u_m. -/
def OrdinaryWidth {m n : ℕ} (H : (Fin m → Fin n) → ℂ) (r : ℕ) : Prop :=
  ∃ u : Fin r → Fin m → Fin n → ℂ,
    ∀ i, H i = ∑ j, ∏ k, u j k (i k)

/-- A sum of r terms c v^{⊗m}. -/
def SymmetricWidth {m n : ℕ} (H : (Fin m → Fin n) → ℂ) (r : ℕ) : Prop :=
  ∃ c : Fin r → ℂ, ∃ v : Fin r → Fin n → ℂ,
    ∀ i, H i = ∑ j, c j * ∏ k, v j (i k)

/-- OP-00211: Comon's exact-rank conjecture for Hankel tensors -/
def _root_.RegistryProblems.Problem_OP_00211 : Prop :=
  ∀ m n : ℕ, 3 ≤ m → 2 ≤ n →
    ∀ h : Fin (m * (n - 1) + 1) → ℂ, ∀ r : ℕ,
      OrdinaryWidth (Hankel h) r ↔ SymmetricWidth (Hankel h) r

end
end RegistryProblems.OP_00211
