/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Raw Count Reciprocal

Adapted from the user-provided archive `combined_audited_lean_sources.zip`,
which describes these declarations as extracted from
`combined_audited_manuscript(4).pdf`. The manuscript itself was not bundled
with this continuation, so this module records archive provenance rather than
claiming page-level source verification.
-/

open scoped BigOperators

namespace RiemannResearch.RH.CombinedAudited

variable {α : Type*}

/-- An unweighted sum over a finite zero set counts the zeros and nothing more. -/
@[simp] theorem raw_unweighted_sum_eq_card (s : Finset α) :
    (∑ _z ∈ s, (1 : ℕ)) = s.card := by
  simp

/-- Pointwise reciprocal comparison used by running-maximum criteria. -/
theorem reciprocal_le_reciprocal_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 / b ≤ 1 / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  exact (div_le_div_iff₀ hb ha).2 (by simpa using hab)

/-- Finite partial sums inherit the reciprocal comparison. -/
theorem reciprocal_partial_sum_comparison
    (A B : ℕ → ℝ) (N : ℕ)
    (hA : ∀ n, 0 < A n) (hAB : ∀ n, A n ≤ B n) :
    (∑ n ∈ Finset.range N, 1 / B n) ≤
      ∑ n ∈ Finset.range N, 1 / A n := by
  apply Finset.sum_le_sum
  intro n hn
  exact reciprocal_le_reciprocal_of_le (hA n) (hAB n)

end RiemannResearch.RH.CombinedAudited
