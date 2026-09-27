/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite weighted energy comparison with a controlled signed error

These elementary estimates compare the energy of a finite approximation
with that of its target once the energy of their difference is controlled.
For the damped Mobius consumer, that difference must first be formed using
the exact signed density-tail identity; the present inequalities do not
replace the tail by a sum of atomwise absolute errors.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis

/-- A weighted finite energy is bounded by twice the comparison energy
plus twice the energy of the signed difference. -/
theorem sum_weighted_sq_le_two_mul_add_sub_sq
    {ι : Type*} (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (f i) ^ 2) ≤
      2 * (∑ i ∈ s, w i * (g i) ^ 2) +
      2 * (∑ i ∈ s, w i * (f i - g i) ^ 2) := by
  calc
    (∑ i ∈ s, w i * (f i) ^ 2) ≤
        ∑ i ∈ s, (2 * (w i * (g i) ^ 2) +
          2 * (w i * (f i - g i) ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : (f i) ^ 2 ≤ 2 * (g i) ^ 2 + 2 * (f i - g i) ^ 2 := by
        nlinarith [sq_nonneg (f i - 2 * g i)]
      have hm := mul_le_mul_of_nonneg_left hp (hw i hi)
      nlinarith
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- A uniform bound on the energy of the signed error gives energy
comparison in both directions, with the same explicit additive constant. -/
theorem sum_weighted_sq_comparison_of_sub_sq_le
    {ι : Type*} (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (K : ℝ)
    (herror : (∑ i ∈ s, w i * (f i - g i) ^ 2) ≤ K) :
    ((∑ i ∈ s, w i * (f i) ^ 2) ≤
      2 * (∑ i ∈ s, w i * (g i) ^ 2) + 2 * K) ∧
    ((∑ i ∈ s, w i * (g i) ^ 2) ≤
      2 * (∑ i ∈ s, w i * (f i) ^ 2) + 2 * K) := by
  have hfg := sum_weighted_sq_le_two_mul_add_sub_sq s w f g hw
  have hgf := sum_weighted_sq_le_two_mul_add_sub_sq s w g f hw
  have heq : (∑ i ∈ s, w i * (g i - f i) ^ 2) =
      ∑ i ∈ s, w i * (f i - g i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq] at hgf
  exact ⟨by linarith, by linarith⟩

end RiemannResearch.Analysis
