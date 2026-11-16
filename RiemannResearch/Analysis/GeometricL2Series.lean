/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Summing geometrically controlled square moments

A weighted finite Cauchy inequality retains every summand. Absolute
convergence and dominated convergence then justify the passage to the
ordinary infinite sum, with no factor depending on the number of blocks.
The concrete consumer is the exponentially smoothed divisor series.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Real

theorem summable_shifted_pow_mul_geometric {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (k m : ℕ) : Summable (fun j : ℕ => (j + m : ℝ) ^ k * q ^ j) := by
  have h := (summable_nat_add_iff m).2
    (summable_pow_mul_geometric_of_norm_lt_one (r := q) k
      (by simpa [Real.norm_eq_abs, abs_of_pos hq] using hq1))
  have hq0 : q ^ m ≠ 0 := pow_ne_zero _ hq.ne'
  have hmul := h.mul_right (q ^ m)⁻¹
  simpa only [Nat.cast_add, pow_add, mul_assoc, mul_inv_cancel₀ hq0, mul_one] using hmul

end Real

namespace Complex

theorem norm_sum_sq_le_geometric (s : Finset ℕ) (F : ℕ → ℂ) :
    ‖∑ j ∈ s, F j‖ ^ 2 ≤ 2 * ∑ j ∈ s, (9 / 4 : ℝ) ^ j * ‖F j‖ ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun j => (2 / 3 : ℝ) ^ j) (fun j => (3 / 2 : ℝ) ^ j * ‖F j‖)
  have hid (j : ℕ) : (2 / 3 : ℝ) ^ j * ((3 / 2 : ℝ) ^ j * ‖F j‖) = ‖F j‖ := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  have hp (a : ℝ) (j : ℕ) : (a ^ j) ^ 2 = (a ^ 2) ^ j := by
    rw [← pow_mul, mul_comm j 2, pow_mul]
  simp_rw [hid, mul_pow, hp] at hcs
  norm_num at hcs
  have hgeom : Summable (fun j : ℕ => (4 / 9 : ℝ) ^ j) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hs : (∑ j ∈ s, (4 / 9 : ℝ) ^ j) ≤ 2 := by
    apply le_trans (Summable.sum_le_tsum s (by intros; positivity) hgeom)
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc
    _ ≤ (∑ j ∈ s, ‖F j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := hcs.trans (mul_le_mul_of_nonneg_right hs (by positivity))

/-- L² summation with a fixed geometric Cauchy weight; no cutoff-dependent factor. -/
theorem integral_norm_tsum_sq_le_geometric
    (F : ℕ → ℝ → ℂ) (b : ℕ → ℝ)
    (hF : ∀ j, Continuous (F j)) (hb : Summable b)
    (hbound : ∀ j t, ‖F j t‖ ≤ b j)
    {H T A : ℝ} (hHT : H ≤ T) (hA : 0 ≤ A) (k : ℕ)
    (hm : ∀ j, (∫ t in H..T, ‖F j t‖ ^ 2) ≤
      A * ((j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j)) :
    (∫ t in H..T, ‖∑' j, F j t‖ ^ 2) ≤
      2 * A * (∑' j : ℕ, (j + 2 : ℝ) ^ k * (9 / 16 : ℝ) ^ j) := by
  have hb0 (j : ℕ) : 0 ≤ b j := (norm_nonneg (F j 0)).trans (hbound j 0)
  have hsum (t : ℝ) : Summable (fun j => F j t) :=
    Summable.of_norm_bounded hb (fun j => hbound j t)
  have hpoly := Real.summable_shifted_pow_mul_geometric
    (q := (9 / 16 : ℝ)) (by norm_num) (by norm_num) k 2
  have hfinite (J : ℕ) :
      (∫ t in H..T, ‖∑ j ∈ Finset.range J, F j t‖ ^ 2) ≤
        2 * A * (∑' j : ℕ, (j + 2 : ℝ) ^ k * (9 / 16 : ℝ) ^ j) := by
    have hc : Continuous (fun t => ∑ j ∈ Finset.range J, F j t) :=
      continuous_finsetSum _ (fun j _ => hF j)
    calc
      _ ≤ ∫ t in H..T, 2 * ∑ j ∈ Finset.range J, (9 / 4 : ℝ) ^ j * ‖F j t‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on hHT
          (hc.norm.pow 2 |>.intervalIntegrable H T)
          ((continuous_finsetSum _ (fun j _ => (hF j).norm.pow 2 |>.const_mul _)).const_mul 2
            |>.intervalIntegrable H T)
        intro t ht
        exact norm_sum_sq_le_geometric _ (fun j => F j t)
      _ = 2 * ∑ j ∈ Finset.range J,
          (9 / 4 : ℝ) ^ j * (∫ t in H..T, ‖F j t‖ ^ 2) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
        · simp_rw [intervalIntegral.integral_const_mul]
        · intro j hj
          exact ((hF j).norm.pow 2 |>.const_mul _).intervalIntegrable H T
      _ ≤ 2 * ∑ j ∈ Finset.range J,
          (9 / 4 : ℝ) ^ j * (A * ((j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hm j) (by positivity))
      _ = 2 * A * ∑ j ∈ Finset.range J, (j + 2 : ℝ) ^ k * (9 / 16 : ℝ) ^ j := by
        have he (j : ℕ) :
            (9 / 4 : ℝ) ^ j * (A * ((j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j)) =
              A * ((j + 2 : ℝ) ^ k * (9 / 16 : ℝ) ^ j) := by
          have hq : (9 / 4 : ℝ) ^ j * (1 / 4 : ℝ) ^ j = (9 / 16 : ℝ) ^ j := by
            rw [← mul_pow]
            norm_num
          rw [← hq]
          ring
        simp_rw [he]
        rw [← Finset.mul_sum]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (by intros; positivity) hpoly) (by positivity)
  have hlim : Tendsto
      (fun J => ∫ t in H..T, ‖∑ j ∈ Finset.range J, F j t‖ ^ 2) atTop
      (𝓝 (∫ t in H..T, ‖∑' j, F j t‖ ^ 2)) := by
    simp_rw [intervalIntegral.integral_of_le hHT]
    apply tendsto_integral_of_dominated_convergence
      (fun _ : ℝ => (∑' j, b j) ^ 2)
    · intro J
      exact ((continuous_finsetSum _ (fun j _ => hF j)).norm.pow 2).aestronglyMeasurable
    · exact integrable_const _
    · intro J
      apply Eventually.of_forall
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sum_le _ _).trans
        ((Finset.sum_le_sum (fun j _ => hbound j t)).trans
          (Summable.sum_le_tsum _ (fun j _ => hb0 j) hb))
    · apply Eventually.of_forall
      intro t
      exact ((hsum t).hasSum.tendsto_sum_nat.norm).pow 2
  exact le_of_tendsto hlim (Eventually.of_forall hfinite)
end Complex
