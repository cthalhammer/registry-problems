/-
  OP-00111: Full nonnegative rank of the quadratic correlation matrix

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00111

      theorem resolution : RegistryProblems.Problem_OP_00111 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/nonnegative-and-positive-factorizations/NR-03/lean/NLA/NR03/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The definitions targetStatement uses are copied
  verbatim without their set_option, noncomputable-section and namespace lines;
  targetStatement itself becomes the body; left out as unused by it:
  castNatMatrix, scaledRightFactor and HasScaledIntegerCertificate (the n = 7
  certificate machinery).
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00111
noncomputable section

open scoped BigOperators Matrix

/-- A Boolean vector with exactly `n` coordinates. -/
abbrev BoolVec (n : ℕ) := Fin n → Bool

/-- The real value represented by one Boolean coordinate. -/
def boolToReal (b : Bool) : ℝ := if b = true then 1 else 0

/-- The ordinary real dot product of two Boolean vectors. -/
def boolDot {n : ℕ} (a b : BoolVec n) : ℝ :=
  ∑ i : Fin n, boolToReal (a i) * boolToReal (b i)

/-- The complete prescribed quadratic correlation matrix.  The subtraction is
over `ℝ`, so entries with dot product greater than one are retained exactly. -/
def cMatrix (n : ℕ) : Matrix (BoolVec n) (BoolVec n) ℝ :=
  fun a b => (1 - boolDot a b) ^ 2

/-- Entrywise nonnegativity of a real matrix. -/
def EntrywiseNonnegative {ι κ : Type} (X : Matrix ι κ ℝ) : Prop :=
  ∀ i j, 0 ≤ X i j

/-- A genuine real nonnegative factorization of a matrix through `Fin r`. -/
def FactorizationData {ι κ : Type} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ) (r : ℕ)
    (W : Matrix ι (Fin r) ℝ) (H : Matrix (Fin r) κ ℝ) : Prop :=
  EntrywiseNonnegative W ∧ EntrywiseNonnegative H ∧ W * H = X

/-- Existence of a real entrywise-nonnegative factorization of width `r`. -/
def HasNonnegativeFactorization {ι κ : Type} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ) (r : ℕ) : Prop :=
  ∃ W : Matrix ι (Fin r) ℝ, ∃ H : Matrix (Fin r) κ ℝ,
    FactorizationData X r W H

/-- The actual minimum width whenever at least one finite factorization exists.
The value `0` in the impossible branch is only a totalization; all rank
claims below carry the explicit existence premise or establish it first. -/
def nonnegativeRank {ι κ : Type} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ) : ℕ :=
  by
    classical
    exact if h : ∃ r : ℕ, HasNonnegativeFactorization X r then Nat.find h else 0

/-- OP-00111: Full nonnegative rank of the quadratic correlation matrix -/
def _root_.RegistryProblems.Problem_OP_00111 : Prop :=
  ∀ n : ℕ, 3 ≤ n → nonnegativeRank (cMatrix n) = 2 ^ n

end
end RegistryProblems.OP_00111
