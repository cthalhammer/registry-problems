/-
  OP-00102: Nobori's spectral-middle-factor commutator conjecture

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00102

      theorem resolution : RegistryProblems.Problem_OP_00102 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-13/lean/NLA/MI13/Definitions.lean

  Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the statement of the binder theorem
  canonical_rectangular_bound (Challenge.lean, proved in NLA/MI13/Complete.lean)
  turned into a closed Prop with its implicit {m n} made explicit; the preamble
  copies Rect, EuclideanVector, EntrySpace, euclideanLin, euclideanCLM,
  spectralNorm, flatten, frobeniusNorm and singularValue verbatim with their
  open line, leaves out Square and all other definitions (SVD, commutator,
  padding and sharpness objects used only by other exports), and drops
  set_option autoImplicit false, the namespace, the noncomputable section and
  the two closing end lines.
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic

namespace RegistryProblems.OP_00102
noncomputable section

open scoped BigOperators Matrix

abbrev Rect (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ
abbrev EuclideanVector (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev EntrySpace (m n : ℕ) := EuclideanSpace ℂ (Fin m × Fin n)

def euclideanLin {m n : ℕ} (A : Rect m n) :
    EuclideanVector n →ₗ[ℂ] EuclideanVector m := Matrix.toEuclideanLin A

def euclideanCLM {m n : ℕ} (A : Rect m n) :
    EuclideanVector n →L[ℂ] EuclideanVector m :=
  (euclideanLin A).toContinuousLinearMap

def spectralNorm {m n : ℕ} (A : Rect m n) : ℝ := ‖euclideanCLM A‖

def flatten {m n : ℕ} (A : Rect m n) : EntrySpace m n :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

def frobeniusNorm {m n : ℕ} (A : Rect m n) : ℝ := ‖flatten A‖

/-- Mathlib's actual decreasing, nonnegative, zero-extended singular values. -/
def singularValue {m n : ℕ} (A : Rect m n) (k : ℕ) : ℝ :=
  (euclideanLin A).singularValues k

/-- OP-00102: Nobori's spectral-middle-factor commutator conjecture -/
def _root_.RegistryProblems.Problem_OP_00102 : Prop :=
  ∀ (m n : ℕ), 2 ≤ m → 2 ≤ n → ∀ (A C : Rect m n) (B : Rect n m),
    frobeniusNorm (A * B * C - C * B * A) ^ 2 ≤
      2 * spectralNorm B ^ 2 * (singularValue A 0 ^ 2 + singularValue A 1 ^ 2) *
        frobeniusNorm C ^ 2

end
end RegistryProblems.OP_00102
