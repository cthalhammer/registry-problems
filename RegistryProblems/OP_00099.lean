/-
  OP-00099: A universal block-norm characterization of essentially Hermitian matrices

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00099

      theorem resolution : RegistryProblems.Problem_OP_00099 := ...

  Formalised by George Stepaniants, not by clopen.solutions:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e375a6fc0a12df52c4f5a38b53df78b837e1c390/matrix-inequalities-and-norms/MI-04/lean/NLA/MI04/Definitions.lean

  Copyright (c) 2026 George Stepaniants.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The body is the statement of the binder theorem
  universal_positive_block_essentially_hermitian (Challenge.lean, same in
  NLA/MI04/Conclusion.lean) turned into a closed Prop with its implicit {n} made
  explicit; the preamble copies CMatrix, Square and spectralNorm verbatim from
  Definitions.lean, with the named section FiniteCoordinates turned into an
  anonymous section/end (a named end is not allowed) around its variable line,
  leaves out every other definition (unused by the body), and drops set_option
  autoImplicit false, the namespace, the noncomputable section, and
  Challenge.lean's extra open scoped Topology / open Filter, which the body does
  not need.
-/

import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Order

namespace RegistryProblems.OP_00099
noncomputable section

open scoped BigOperators ComplexOrder

abbrev CMatrix (ι : Type*) := Matrix ι ι ℂ
abbrev Square (n : ℕ) := CMatrix (Fin n)

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual complex Euclidean operator norm, never the default Pi matrix norm. -/
def spectralNorm (M : CMatrix ι) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖

end

/-- OP-00099: A universal block-norm characterization of essentially Hermitian matrices -/
def _root_.RegistryProblems.Problem_OP_00099 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (X : Square n),
    (∀ A B : Square n, A.IsHermitian → B.IsHermitian →
      (Matrix.fromBlocks A X X.conjTranspose B).PosSemidef →
        spectralNorm (Matrix.fromBlocks A X X.conjTranspose B) ≤ spectralNorm (A + B)) →
    ∃ K : Square n, K.IsHermitian ∧ ∃ α β : ℂ,
      X = α • K + β • (1 : Square n)

end
end RegistryProblems.OP_00099
