/-
  OP-00104: Freewan–Hayajneh inequality for sums of weighted geometric means

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00104

      theorem resolution : RegistryProblems.Problem_OP_00104 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-21/lean/NLA/MI21/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Copied Mat, spectralPower, geometricMean,
  IsUnitaryInvariantNorm, leftMatrix and rightMatrix verbatim with their two
  open lines, left out operatorNorm, GeometricMeanNormConjecture (its body is
  the body) and the witness definitions, none of which the body uses, and
  dropped set_option autoImplicit false, the namespace and the noncomputable
  section lines.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace RegistryProblems.OP_00104
noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Real powers from the actual continuous functional calculus. On the positive
definite inputs of the conjecture this is spectral matrix exponentiation. -/
def spectralPower {n : ℕ} (A : Mat n) (r : ℝ) : Mat n := CFC.rpow A r

/-- The weighted geometric mean in the exact order written in the canonical target.
The exponents `1/2`, `-1/2` and `t` are real spectral powers. -/
def geometricMean {n : ℕ} (A B : Mat n) (t : ℝ) : Mat n :=
  spectralPower A (1 / 2) *
    spectralPower (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)) t *
      spectralPower A (1 / 2)

/-- A complex norm on the full matrix vector space, with independent left and
right unitary invariance. These are the usual norm axioms, not an operator-norm
restriction. Both unitary inverse identities are stated explicitly. -/
def IsUnitaryInvariantNorm {n : ℕ} (ν : Mat n → ℝ) : Prop :=
  (∀ X, 0 ≤ ν X) ∧
  (∀ X, ν X = 0 ↔ X = 0) ∧
  (∀ X Y, ν (X + Y) ≤ ν X + ν Y) ∧
  (∀ (z : ℂ) X, ν (z • X) = ‖z‖ * ν X) ∧
  (∀ U V X : Mat n, Uᴴ * U = 1 → U * Uᴴ = 1 →
    Vᴴ * V = 1 → V * Vᴴ = 1 → ν (U * X * V) = ν X)

/-- The sum of the powered weighted means on the left of MI-21. -/
def leftMatrix {m n : ℕ} (A B : Fin m → Mat n) (s t r : ℝ) : Mat n :=
  ∑ i, spectralPower (geometricMean (spectralPower (A i) s)
    (spectralPower (B i) s) t) r

/-- The right side uses the actual aggregate sums and the original order of
the three noncommuting factors before its final real power. -/
def rightMatrix {m n : ℕ} (A B : Fin m → Mat n) (s t r p : ℝ) : Mat n :=
  spectralPower
    (spectralPower (∑ i, A i) ((1 - t) * s * r * p / 2) *
      spectralPower (∑ i, B i) (t * s * r * p) *
        spectralPower (∑ i, A i) ((1 - t) * s * r * p / 2)) (1 / p)

/-- OP-00104: Freewan–Hayajneh inequality for sums of weighted geometric means -/
def _root_.RegistryProblems.Problem_OP_00104 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ A B : Fin m → Mat n,
    (∀ i, (A i).PosDef) → (∀ i, (B i).PosDef) →
    ∀ t s r p : ℝ, 0 ≤ t → t ≤ 1 → 0 < s → 0 < r → 0 < p → 1 ≤ s * r →
    ∀ ν : Mat n → ℝ, IsUnitaryInvariantNorm ν →
      ν (leftMatrix A B s t r) ≤ ν (rightMatrix A B s t r p)

end
end RegistryProblems.OP_00104
