/-
  OP-00124: Nonnegative H-eigenvalue inheritance from odd-order Hankel tensors

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00124

      theorem resolution : RegistryProblems.Problem_OP_00124 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/tensor-computations/TR-15/lean/NLA/TR15/Definitions.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the body of InheritanceConjecture copied
  verbatim; the witness and nonvacuity definitions (witnessGenerator,
  witnessLower, witnessUpper, witnessUpperVector, rootPolynomial,
  lowerEigenvalue, lowerEigenvector), the module docstring and the target def
  itself are left out, and set_option, namespace, noncomputable-section and end
  lines are dropped (generatorIndex, prependIndex and lowerTensor keep their
  in-definition proofs by calc/simp/omega).
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00124
noncomputable section

open scoped BigOperators

/-- A real tensor with `s` slots, each of dimension `N`. -/
abbrev Tensor (s N : ℕ) := (Fin s → Fin N) → ℝ

/-- Sum of zero-based tensor indices as an actual index into the finite
generating vector. The proof establishes the bound, without a default value. -/
def generatorIndex {s N : ℕ} (indices : Fin s → Fin N) :
    Fin (s * (N - 1) + 1) :=
  ⟨∑ j, (indices j).val, by
    have hle : (∑ j : Fin s, (indices j).val) ≤ s * (N - 1) := by
      calc
        (∑ j : Fin s, (indices j).val) ≤ ∑ _j : Fin s, (N - 1) :=
          Finset.sum_le_sum (fun j _ => Nat.le_sub_one_of_lt (indices j).isLt)
        _ = s * (N - 1) := by simp
    omega⟩

/-- Every entry is taken from the same finite generating vector. -/
def hankelTensor (s N : ℕ) (h : Fin (s * (N - 1) + 1) → ℝ) : Tensor s N :=
  fun indices => h (generatorIndex indices)

/-- Prepend the uncontracted coordinate to the `s-1` contracted indices.
For positive order this is the usual tuple `(i, indices 0, …)`.
The total definition at order zero is never used by the conjecture. -/
def prependIndex {s N : ℕ} (i : Fin N) (indices : Fin (s - 1) → Fin N) :
    Fin s → Fin N :=
  fun j => if hj : j.val = 0 then i else
    indices ⟨j.val - 1, by have := j.isLt; omega⟩

/-- The full H-eigenvalue contraction: sum over all ordered `(s-1)`-tuples,
with one factor of `x` for each contracted slot. There are no multinomial
weights because every ordered tuple appears separately. -/
def contraction {s N : ℕ} (T : Tensor s N) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => ∑ indices : Fin (s - 1) → Fin N,
    T (prependIndex i indices) * ∏ j : Fin (s - 1), x (indices j)

/-- A genuine real H-eigenpair, including the nonzero-vector requirement. -/
def IsHEigenpair {s N : ℕ} (T : Tensor s N) (eigenvalue : ℝ)
    (x : Fin N → ℝ) : Prop :=
  x ≠ 0 ∧ ∀ i, contraction T x i = eigenvalue * x i ^ (s - 1)

/-- Every real H-eigenpair has a nonnegative real eigenvalue. This is exactly
the canonical absence of a negative real H-eigenvalue; existence is not assumed. -/
def HasNoNegativeHEigenvalues {s N : ℕ} (T : Tensor s N) : Prop :=
  ∀ (eigenvalue : ℝ) (x : Fin N → ℝ), IsHEigenpair T eigenvalue x →
    0 ≤ eigenvalue

/-- The original lower tensor: order `m`, dimension `q*(n-1)+1`.
The finite cast only identifies the equal generating-vector lengths. -/
def lowerTensor (m q n : ℕ) (h : Fin (q * m * (n - 1) + 1) → ℝ) :
    Tensor m (q * (n - 1) + 1) :=
  hankelTensor m (q * (n - 1) + 1)
    (fun i => h (Fin.cast (by simp [Nat.mul_comm, Nat.mul_assoc]) i))

/-- The original higher tensor: order `q*m`, dimension `n`, using exactly `h`. -/
def upperTensor (m q n : ℕ) (h : Fin (q * m * (n - 1) + 1) → ℝ) :
    Tensor (q * m) n :=
  hankelTensor (q * m) n h

/-- Every parameter restriction from the original conjecture. -/
def Admissible (m q n : ℕ) : Prop :=
  Odd m ∧ 3 ≤ m ∧ 2 ≤ q ∧ 2 ≤ n

/-- OP-00124: Nonnegative H-eigenvalue inheritance from odd-order Hankel tensors -/
def _root_.RegistryProblems.Problem_OP_00124 : Prop :=
  ∀ (m q n : ℕ), Admissible m q n →
    ∀ h : Fin (q * m * (n - 1) + 1) → ℝ,
      HasNoNegativeHEigenvalues (lowerTensor m q n h) →
        HasNoNegativeHEigenvalues (upperTensor m q n h)

end
end RegistryProblems.OP_00124
