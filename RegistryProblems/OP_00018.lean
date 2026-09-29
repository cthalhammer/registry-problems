/-
  OP-00018: The 1/3–2/3 conjecture for finite posets

  Canonical statement for clopen.solutions. GENERATED FILE -- do not edit.
  Produced by `manage.py build_problems_package` from the formalization marked
  canonical in the registry. The declaration name is derived from the problem's
  permanent ID, so it never changes once published.

  A submission resolves the problem by proving the constant, or refutes it by
  proving its negation:

      import RegistryProblems.OP_00018

      theorem resolution : RegistryProblems.Problem_OP_00018 := ...

  Formalised by The Formal Conjectures Authors, not by clopen.solutions:
  https://github.com/google-deepmind/formal-conjectures/blob/0771383387505c96d1b2f6a3d35088ad00892c5c/FormalConjectures/Wikipedia/conjecture_1_3_to_2_3.lean#L30

  Copyright 2025 The Formal Conjectures Authors.
  Licensed under Apache-2.0; its text is LICENSES/Apache-2.0.txt in this
  package.

  Changed from the source: restated as the definition below, named after this
  problem's permanent ID. The source's `answer(sorry) ↔`, a placeholder for
  whether the answer is yes or no, is removed, leaving the proposition it asks
  about. That proposition is as Lean prints it, checked to elaborate to the same
  term. The source's name, attributes, docstring and proof are not carried over.
-/

import Mathlib

namespace RegistryProblems

/-- OP-00018: The 1/3–2/3 conjecture for finite posets -/
def Problem_OP_00018 : Prop :=
  ∀ (P : Type) [Finite P] [inst : PartialOrder P],
      (¬Std.Total fun (x1 x2 : P) ↦ x1 ≤ x2) →
        ∀ (total_ext : Set (P →o ℕ)),
          (∀ (σ : P →o ℕ), σ ∈ total_ext ↔ Set.range (⇑σ : P → ℕ) = Set.Icc (1 : ℕ) (Nat.card P)) →
            ∃ (x : P) (y : P),
              (↑(Set.ncard {σ : P →o ℕ | σ ∈ total_ext ∧ (σ : P → ℕ) x < (σ : P → ℕ) y}) : ℚ) /
                  (↑(Set.ncard total_ext) : ℚ) ∈
                Set.Icc (1 / 3 : ℚ) (2 / 3 : ℚ)

end RegistryProblems
