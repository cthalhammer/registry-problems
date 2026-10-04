/-
  OP-00094: Degree coverage with seven matrix multiplications

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00094

      theorem resolution : RegistryProblems.Problem_OP_00094 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-functions-and-stability/MF-14/lean/NLA/MF14/Definitions.lean

  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The theorem is `¬ IsGreatest NLA.MF14.coveredDegrees
  42`, so the body is `IsGreatest coveredDegrees 42` with the reference
  unqualified; only the definitions it uses (Poly, CoefficientSpace,
  GatePolynomials, availableGenerators, availableSpace, IsSevenGateCircuit,
  IsSevenProductOutput, coefficientVector, outputVectors, vanishingHull,
  sevenProductClosure, degreePlane, CoversDegree, coveredDegrees) are copied
  with the file's `open Set Polynomial`, leaving out Parameters,
  IsAtMostSevenProductOutput, the 49-parameter family and HasDoublingDegrees.
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Span.Defs

namespace RegistryProblems.OP_00094
noncomputable section

open Set Polynomial

abbrev Poly := Polynomial ℂ
abbrev CoefficientSpace := Fin 129 → ℂ
abbrev GatePolynomials := Fin 7 → Poly

/-- Available polynomials before zero-based gate `k`: initial `1, X` and
the outputs of strictly earlier multiplication gates. -/
def availableGenerators (q : GatePolynomials) (k : ℕ) : Set Poly :=
  {1, X} ∪ {p | ∃ j : Fin 7, j.val < k ∧ p = q j}

def availableSpace (q : GatePolynomials) (k : ℕ) : Submodule ℂ Poly :=
  Submodule.span ℂ (availableGenerators q k)

/-- Seven chronological multiplication gates. Free complex linear
combinations are represented by membership in the available vector space. -/
def IsSevenGateCircuit (q : GatePolynomials) : Prop :=
  ∀ k : Fin 7, ∃ u v : Poly,
    u ∈ availableSpace q k.val ∧ v ∈ availableSpace q k.val ∧ q k = u * v

/-- Outputs after seven gates; circuits with fewer gates will be identified
with these by proving zero-gate padding, not by an assumed equivalence. -/
def IsSevenProductOutput (p : Poly) : Prop :=
  ∃ q : GatePolynomials, IsSevenGateCircuit q ∧ p ∈ availableSpace q 7

def coefficientVector (p : Poly) : CoefficientSpace :=
  fun i => p.coeff i.val

def outputVectors : Set CoefficientSpace :=
  coefficientVector '' {p | IsSevenProductOutput p}

/-- The exact canonical closure: simultaneous zero set of every complex
polynomial equation vanishing on the given set of full coefficient vectors. -/
def vanishingHull (S : Set CoefficientSpace) : Set CoefficientSpace :=
  {z | ∀ F : MvPolynomial (Fin 129) ℂ,
    (∀ w ∈ S, MvPolynomial.eval w F = 0) → MvPolynomial.eval z F = 0}

def sevenProductClosure : Set CoefficientSpace := vanishingHull outputVectors

/-- The full coefficient plane, including zero and all degrees below `d`. -/
def degreePlane (d : ℕ) : Set CoefficientSpace :=
  {z | ∀ i : Fin 129, d < i.val → z i = 0}

def CoversDegree (d : ℕ) : Prop := degreePlane d ⊆ sevenProductClosure

def coveredDegrees : Set ℕ := {d | d ≤ 128 ∧ CoversDegree d}

/-- OP-00094: Degree coverage with seven matrix multiplications -/
def _root_.RegistryProblems.Problem_OP_00094 : Prop :=
  IsGreatest coveredDegrees 42

end
end RegistryProblems.OP_00094
