/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualMicroscopicHorizontalConcentration
import RiemannResearch.Analysis.ConreyHorizontalStopLoss

/-!
# Microscopic concentration via one bounded stop-loss difference

For the empirical law on zero occurrences the difference of the stop-loss
values at 0 and 1 is exactly the first moment clipped at 1. Its vanishing
detects microscopic concentration without an exponential tail input.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem microscopicExcess_sub_one_eq_clipped {T : ℝ} (hT : 1 < T) :
    microscopicExcess T 0 - microscopicExcess T 1 =
      (∑ j : Copies T, min (copyDisplacement T j * Real.log T) 1) / (Ncount 0 T : ℝ) := by
  unfold microscopicExcess
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have h := mul_nonneg (abs_nonneg (j.1.1.re - 1 / 2)) (Real.log_pos hT).le
  change 0 ≤ copyDisplacement T j * Real.log T at h
  rw [sub_zero, max_eq_left h]
  rcases le_total (copyDisplacement T j * Real.log T) 1 with hle | hge
  · rw [min_eq_left hle, max_eq_right (sub_nonpos.mpr hle), sub_zero]
  · rw [min_eq_right hge, max_eq_left (sub_nonneg.mpr hge)]
    ring

/-- Both comparisons hold at finite height, including atoms exactly at the strike. -/
theorem clipped_excess_tail_bounds {T δ : ℝ} (hT : 1 < T) (hδ : 0 < δ) :
    let D := microscopicExcess T 0 - microscopicExcess T 1
    let P := strictTail T (δ / Real.log T) / (Ncount 0 T : ℝ)
    min δ 1 * P ≤ D ∧ D ≤ δ + P := by
  classical
  dsimp only
  rw [microscopicExcess_sub_one_eq_clipped hT]
  let ind := fun j : Copies T => if δ / Real.log T < copyDisplacement T j then (1 : ℝ) else 0
  have ht : strictTail T (δ / Real.log T) = ∑ j : Copies T, ind j := rfl
  have hL := Real.log_pos hT
  have h (j : Copies T) :
      min δ 1 * ind j ≤ min (copyDisplacement T j * Real.log T) 1 ∧
      min (copyDisplacement T j * Real.log T) 1 ≤ δ + ind j := by
    dsimp only [ind]
    split_ifs with hx
    · rw [mul_one]
      exact ⟨min_le_min_right 1 ((div_lt_iff₀ hL).mp hx).le,
        (min_le_right _ _).trans (by linarith)⟩
    · simp only [add_zero, mul_zero]
      exact ⟨le_min (mul_nonneg (abs_nonneg _) hL.le) zero_le_one,
        (min_le_left _ _).trans ((le_div_iff₀ hL).mp (not_lt.mp hx))⟩
  rw [ht, ← mul_div_assoc, Finset.mul_sum]
  constructor
  · exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => (h j).1) (Nat.cast_nonneg _)
  · have hs := div_le_div_of_nonneg_right
      (Finset.sum_le_sum (s := Finset.univ) fun j _ => (h j).2)
      (Nat.cast_nonneg (Ncount 0 T) (α := ℝ))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_copies,
      nsmul_eq_mul, add_div] at hs
    by_cases hz : (Ncount 0 T : ℝ) = 0
    · simp [hz, hδ.le]
    · simpa [hz, mul_div_cancel_left₀] using hs

/-- One bounded observable characterizes the ordinary-ordinate horizontal
hypothesis at every fixed microscopic threshold. The difference retains the
cancellation between the two finite-height stop-loss evaluations. -/
theorem microscopicHorizontalConcentration_iff_clipped_excess :
    MicroscopicHorizontalConcentration ↔
      Tendsto (fun T => microscopicExcess T 0 - microscopicExcess T 1) atTop (𝓝 0) := by
  let D := fun T => microscopicExcess T 0 - microscopicExcess T 1
  have hD : ∀ᶠ T : ℝ in atTop, 0 ≤ D T := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T ht
    rw [show D T = _ from microscopicExcess_sub_one_eq_clipped ht]
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg fun j _ => le_min (mul_nonneg (abs_nonneg _) (Real.log_pos ht).le) zero_le_one
  constructor
  · intro hc
    rw [Metric.tendsto_nhds]
    intro ε hε
    have he : 0 < ε / 2 := half_pos hε
    filter_upwards [hD, eventually_gt_atTop (1 : ℝ), (hc (ε / 2) he).eventually_lt_const he]
      with T hd ht htail
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hd]
    exact ((clipped_excess_tail_bounds ht he).2).trans_lt (by linarith only [htail])
  · intro hc δ hδ
    let k : ℝ := min δ 1
    have hk : 0 < k := lt_min hδ zero_lt_one
    apply squeeze_zero'
    · exact Eventually.of_forall fun T => div_nonneg (strictTail_nonneg _ _) (Nat.cast_nonneg _)
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T ht
      exact (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using (clipped_excess_tail_bounds ht hδ).1)
    · simpa only [zero_div] using hc.div_const k

end RiemannResearch.Analysis.ActualZeroOrdinate
