/-
  OP-00097: Polynomial conditioning of the cubic C1 spline Schrödinger Toeplitz family

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00097

      theorem resolution : RegistryProblems.Problem_OP_00097 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-functions-and-stability/MF-22/lean/NLA/MF22/Definitions.lean

  Copyright (c) 2026 George Stepaniants. All rights reserved.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. Only BlockIndex, BlockMatrix, spectralNorm,
  conditionNumber, blockB, blockC and toeplitz are copied with the file's `open
  Polynomial` and `open scoped BigOperators Classical ENNReal`, leaving out
  Square, BlockVector and all transfer-matrix, root, projector and Green-kernel
  definitions; the binder theorem polynomial_conditioning is turned into a
  closed Prop.
-/

import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.ENNReal.Real
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace RegistryProblems.OP_00097
noncomputable section

open Polynomial
open scoped BigOperators Classical ENNReal

abbrev BlockIndex (n : ℕ) := Fin n × Fin 2
abbrev BlockMatrix (n : ℕ) := Matrix (BlockIndex n) (BlockIndex n) ℂ

/-- The genuine induced complex Euclidean operator norm for the displayed
finite index type; no default entrywise matrix norm is substituted. -/
def spectralNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖

/-- Singular matrices have infinite condition number, including when the
totalized nonsingular inverse happens to be zero. -/
def conditionNumber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ≥0∞ :=
  if A.det = 0 then ⊤ else ENNReal.ofReal (spectralNorm A * spectralNorm A⁻¹)

/-- Literal coefficient blocks from the original permanent MF-22 statement. -/
def blockB (k : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k = -1 then (3 / 40 : ℝ) • !![-1, 0; -5, 0]
  else if k = 0 then (3 / 40 : ℝ) • !![0, -5; 16, -5]
  else if k = 1 then (3 / 40 : ℝ) • !![-5, 16; -5, 0]
  else if k = 2 then (3 / 40 : ℝ) • !![0, -5; 0, -1]
  else 0

def blockC (k : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k = -1 then (1 / 80 : ℝ) • !![1, 0; 7, 0]
  else if k = 0 then (1 / 80 : ℝ) • !![24, 7; 0, 25]
  else if k = 1 then (1 / 80 : ℝ) • !![-25, 0; -7, -24]
  else if k = 2 then (1 / 80 : ℝ) • !![0, -7; 0, -1]
  else 0

/-- The original pure Toeplitz truncation, with no corner corrections.
The first coordinate is the block index, and offsets use integer subtraction. -/
def toeplitz (ρ : ℝ) (n : ℕ) : BlockMatrix n := fun row col =>
  Complex.I * (blockB ((row.1.val : ℤ) - (col.1.val : ℤ)) row.2 col.2 : ℂ) -
    (ρ : ℂ) * (blockC ((row.1.val : ℤ) - (col.1.val : ℤ)) row.2 col.2 : ℂ)

/-- OP-00097: Polynomial conditioning of the cubic C1 spline Schrödinger Toeplitz family -/
def _root_.RegistryProblems.Problem_OP_00097 : Prop :=
  ∀ (ρ : ℝ), 0 < ρ →
    ∃ K α : ℝ, 0 < K ∧ 0 ≤ α ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → (toeplitz ρ n).det ≠ 0 ∧
        conditionNumber (toeplitz ρ n) ≤ ENNReal.ofReal (K * Real.rpow (n : ℝ) α)

end
end RegistryProblems.OP_00097
