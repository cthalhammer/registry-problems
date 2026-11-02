/-
  OP-00262: Infinitesimal rigidity detects unique size-two factors in the presence of zeros

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00262

      theorem resolution : RegistryProblems.Problem_OP_00262 := ...

  Formalised by OpenAI Codex AI agents, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/099805ef1ce7347d373e47cccc3b2d7cf580a99e/nonnegative-and-positive-factorizations/PF-05/lean/NLA/Statements/PF05.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions are copied with their doc comments
  edited, and the body is Target's body verbatim; the LeanCert and
  Infrastructure imports, the set_option lines and the #assert commands are
  dropped.
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace

namespace RegistryProblems.OP_00262
noncomputable section

open scoped BigOperators

def Symmetric {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ a b, A a b = A b a

/-- Real symmetry and the ordinary nonnegative quadratic form. -/
def PositiveSemidefinite {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Symmetric A ∧ ∀ x : Fin k → ℝ, 0 ≤ ∑ a, ∑ b, x a * A a b * x b

/-- A size-k PSD factorization, with ordinary matrix multiplication and the
full diagonal trace. Factors are indexed by the rows and columns of M. -/
def Factorization {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin k) (Fin k) ℝ)
    (B : Fin q → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (∀ i, PositiveSemidefinite (A i)) ∧
  (∀ j, PositiveSemidefinite (B j)) ∧
  ∀ i j, M i j = Matrix.trace (A i * B j)

def HasPSDFactorization {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (k : ℕ) : Prop :=
  ∃ A : Fin p → Matrix (Fin k) (Fin k) ℝ,
    ∃ B : Fin q → Matrix (Fin k) (Fin k) ℝ, Factorization M A B

/-- PSD rank exactly two: a factorization of size two and none of size one. -/
def PSDRankTwo {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : Prop :=
  HasPSDFactorization M 2 ∧ ¬ HasPSDFactorization M 1

/-- The trace condition to first order only; the straight segments stay PSD on
one common interval [0, h). -/
def FeasibleDirection {p q : ℕ}
    (A E : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Fin q → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i, Symmetric (E i)) ∧ (∀ j, Symmetric (F j)) ∧
  (∀ i j, Matrix.trace (E i * B j) + Matrix.trace (A i * F j) = 0) ∧
  ∃ h : ℝ, 0 < h ∧ ∀ t : ℝ, 0 ≤ t → t < h →
    (∀ i, PositiveSemidefinite (A i + t • E i)) ∧
    (∀ j, PositiveSemidefinite (B j + t • F j))

/-- Condition (i): one real d common to all factors. -/
def InfinitesimallyRigid {p q : ℕ}
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ E : Fin p → Matrix (Fin 2) (Fin 2) ℝ,
    ∀ F : Fin q → Matrix (Fin 2) (Fin 2) ℝ,
      FeasibleDirection A E B F →
      ∃ d : ℝ, (∀ i, E i = d • A i) ∧ (∀ j, F j = (-d) • B j)

/-- Condition (ii): one S in GL(2, ℝ) for every other size-two factorization. -/
def UniqueUpToCongruence {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ Atilde : Fin p → Matrix (Fin 2) (Fin 2) ℝ,
    ∀ Btilde : Fin q → Matrix (Fin 2) (Fin 2) ℝ,
      Factorization M Atilde Btilde →
      ∃ S : Matrix (Fin 2) (Fin 2) ℝ, S.det ≠ 0 ∧
        (∀ i, Atilde i = S.transpose * A i * S) ∧
        (∀ j, Btilde j = S⁻¹ * B j * (S⁻¹).transpose)

/-- OP-00262: Infinitesimal rigidity detects unique size-two factors in the presence of zeros -/
def _root_.RegistryProblems.Problem_OP_00262 : Prop :=
  ∀ p q : ℕ, ∀ M : Matrix (Fin p) (Fin q) ℝ,
    (∀ i j, 0 ≤ M i j) → M.rank = 3 → PSDRankTwo M →
    ∀ A : Fin p → Matrix (Fin 2) (Fin 2) ℝ,
      ∀ B : Fin q → Matrix (Fin 2) (Fin 2) ℝ,
        Factorization M A B →
        (InfinitesimallyRigid A B ↔ UniqueUpToCongruence M A B)

end
end RegistryProblems.OP_00262
