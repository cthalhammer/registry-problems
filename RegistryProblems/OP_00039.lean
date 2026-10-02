/-
  OP-00039: Zauner's conjecture

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00039

      theorem resolution : RegistryProblems.Problem_OP_00039 := ...

  Formalised by The Formal Conjectures Authors, not by clopen.solutions:
  https://github.com/google-deepmind/formal-conjectures/blob/137aec5c7abd3aa61f7a73138a97279acfc79e93/FormalConjectures/OpenQuantumProblems/23.lean#L366

  Copyright 2026 The Formal Conjectures Authors.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The source's `answer(sorry) ↔`, a placeholder for
  whether the answer is yes or no, is removed, and its definitions HasSICPOVM,
  IsSICFamily, IsNormalized, HasConstantOverlapSq, overlapSq and sicOverlapSq
  are unfolded, with coordinates read through WithLp.ofLp. A SIC-POVM is stated
  as d² unit vectors with pairwise squared overlap 1/(d + 1), which is
  equivalent to an ETF of d² vectors.
-/

import Mathlib

namespace RegistryProblems

/-- OP-00039: Zauner's conjecture -/
def Problem_OP_00039 : Prop :=
  ∀ d : ℕ, 1 ≤ d →
  ∃ Φ : Fin (d ^ 2) → EuclideanSpace ℂ (Fin d),
    (∀ i, ‖Φ i‖ = 1) ∧
      Pairwise fun i j =>
        Complex.normSq (∑ k : Fin d, star ((Φ i).ofLp k) * (Φ j).ofLp k) = ((d : ℝ) + 1)⁻¹

end RegistryProblems
