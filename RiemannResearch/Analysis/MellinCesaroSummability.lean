/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MellinDifferenceBounds
import RiemannResearch.Analysis.MellinStepSeries
import RiemannResearch.Analysis.WeightedComplexPairing
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Summable dual coefficients and the full infinite Cesaro-Mellin bridge

All series are proved summable before they are paired or passed to a limit.
The weight is indexed by positive endpoints, never by the spurious zero atom.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative RH.Pareto

/-- Positive latent-endpoint weights in zero-based sequence coordinates. -/
def conditionalWeight (k : ℕ) : ℝ := mixtureWeight (k + 1)

theorem conditionalWeight_pos (k : ℕ) : 0 < conditionalWeight k := by
  unfold conditionalWeight mixtureWeight
  positivity

/-- The inverse mixture weight has the exact quadratic upper bound needed for the dual. -/
theorem mixtureWeight_inv_le (n : ℕ) (hn : 0 < n) :
    (mixtureWeight n)⁻¹ ≤ 3 * (n : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold mixtureWeight
  rw [inv_div]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  nlinarith

/-- Quantitative weighted dual-square bound for the actual Mellin coefficients. -/
theorem mellinSecond_dual_term_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 0 < n) :
    ‖mellinSecond s n‖ ^ 2 / mixtureWeight n ≤
      3 * ‖s * (s + 1)‖ ^ 2 * (n : ℝ) ^ (-(2 * s.re)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := mellinSecond_norm_le s hs n hn
  have hr : 0 ≤ ‖s * (s + 1)‖ * (n : ℝ) ^ (-s.re - 1) := by positivity
  have hb2 : ‖mellinSecond s n‖ ^ 2 ≤
      ‖s * (s + 1)‖ ^ 2 * ((n : ℝ) ^ (-s.re - 1)) ^ 2 := by
    nlinarith [norm_nonneg (mellinSecond s n)]
  have hq : 0 ≤ (mixtureWeight n)⁻¹ := by unfold mixtureWeight; positivity
  have hp : (n : ℝ) ^ (-s.re - 1) * (n : ℝ) = (n : ℝ) ^ (-s.re) := by
    calc
      _ = (n : ℝ) ^ ((-s.re - 1) + 1) := by rw [Real.rpow_add hnR, Real.rpow_one]
      _ = _ := by congr 1 <;> ring
  have hp2 : ((n : ℝ) ^ (-s.re - 1)) ^ 2 * (n : ℝ) ^ 2 =
      (n : ℝ) ^ (-(2 * s.re)) := by
    rw [← mul_pow, hp, ← Real.rpow_mul_natCast hnR.le]
    congr 1
    ring
  calc
    _ ≤ (‖s * (s + 1)‖ ^ 2 * ((n : ℝ) ^ (-s.re - 1)) ^ 2) *
        (3 * (n : ℝ) ^ 2) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hb2 (mixtureWeight_inv_le n hn) hq (by positivity)
    _ = 3 * ‖s * (s + 1)‖ ^ 2 *
        (((n : ℝ) ^ (-s.re - 1)) ^ 2 * (n : ℝ) ^ 2) := by ring
    _ = _ := by rw [hp2]

/-- The transformed dual is square summable throughout the strict critical half-plane. -/
theorem mellinSecond_dual_summable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun k : ℕ => ‖mellinSecond s (k + 1)‖ ^ 2 / conditionalWeight k) := by
  have hp : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(2 * s.re))) :=
    (Real.summable_nat_rpow.mpr (by linarith : -(2 * s.re) < -1)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  apply (hp.mul_left (3 * ‖s * (s + 1)‖ ^ 2)).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (conditionalWeight_pos k).le)]
  exact mellinSecond_dual_term_le s (by linarith) (k + 1) (Nat.succ_pos k)

/-- Absolute summability of the second-difference coefficients also holds in Re(s)>0. -/
theorem mellinSecond_norm_summable (s : ℂ) (hs : 0 < s.re) :
    Summable (fun k : ℕ => ‖mellinSecond s (k + 1)‖) := by
  have hp : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -s.re - 1 < -1)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  apply (hp.mul_left ‖s * (s + 1)‖).of_norm_bounded
  intro k
  simpa only [norm_norm] using mellinSecond_norm_le s hs (k + 1) (Nat.succ_pos k)

/-- Each bounded arithmetic function has a summable conditional-mean square energy. -/
theorem bounded_mean_energy_summable (F : ℕ → ℂ) (B : ℝ)
    (hB : ∀ n, 0 < n → ‖F n‖ ≤ B) :
    Summable (fun k : ℕ => conditionalWeight k * ‖mean F (k + 1)‖ ^ 2) := by
  have hB0 : 0 ≤ B := (norm_nonneg (F 1)).trans (hB 1 (by omega))
  apply (hasSum_mixtureWeight.summable.mul_right (B ^ 2)).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (conditionalWeight_pos k).le
  have h := mean_norm_le F B hB (k + 1) (Nat.succ_pos k)
  nlinarith [norm_nonneg (mean F (k + 1))]

/-- Convergence of the signed second-difference pairing for every bounded arithmetic function. -/
theorem bounded_second_pairing_summable (s : ℂ) (hs : 0 < s.re)
    (F : ℕ → ℂ) (B : ℝ) (hB : ∀ n, 0 < n → ‖F n‖ ≤ B) :
    Summable (fun k : ℕ => mellinSecond s (k + 1) * mean F (k + 1)) := by
  apply ((mellinSecond_norm_summable s hs).mul_right B).of_norm_bounded
  intro k
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (mean_norm_le F B hB (k + 1) (Nat.succ_pos k)) (norm_nonneg _)

/-- Decay of the exact terminal coefficient in finite summation by parts. -/
theorem terminal_coefficient_norm_le (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    ‖(N : ℂ) * mellinFirst s (N + 1)‖ ≤
      ‖s‖ * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hpow : ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-s.re - 1) =
      ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by
    calc
      _ = ((N + 1 : ℕ) : ℝ) ^ (1 + (-s.re - 1)) := by
        rw [Real.rpow_add hN, Real.rpow_one]
      _ = _ := by congr 1 <;> ring
  rw [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ ((N + 1 : ℕ) : ℝ) *
        (‖s‖ * ((N + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
      mul_le_mul (by exact_mod_cast Nat.le_succ N)
        (mellinFirst_norm_le s hs _ (Nat.succ_pos N)) (norm_nonneg _) (by positivity)
    _ = ‖s‖ * (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by ring
    _ = _ := by rw [hpow]

/-- The retained boundary term actually tends to zero; it is not deleted formally. -/
theorem terminal_pairing_tendsto_zero (s : ℂ) (hs : 0 < s.re)
    (F : ℕ → ℂ) (B : ℝ) (hB : ∀ n, 0 < n → ‖F n‖ ≤ B) :
    Tendsto (fun N : ℕ => (N : ℂ) * mellinFirst s (N + 1) * mean F N) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (norm_nonneg (F 1)).trans (hB 1 (by omega))
  have hmean (N : ℕ) : ‖mean F N‖ ≤ B := by
    rcases Nat.eq_zero_or_pos N with rfl | hn
    · simpa using hB0
    · exact mean_norm_le F B hB N hn
  have ht : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hp := (tendsto_rpow_neg_atTop hs).comp ht
  apply squeeze_zero_norm (a := fun N => (‖s‖ * B) * ((N + 1 : ℕ) : ℝ) ^ (-s.re))
  · intro N
    rw [norm_mul]
    calc
      _ ≤ (‖s‖ * ((N + 1 : ℕ) : ℝ) ^ (-s.re)) * B :=
        mul_le_mul (terminal_coefficient_norm_le s hs N) (hmean N) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · simpa only [Function.comp_def, mul_zero] using hp.const_mul (‖s‖ * B)

/-- Exact full infinite Cesaro-Mellin identity for a bounded Hilbert witness. -/
theorem cesaro_mellin_pairing (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (B : ℝ)
    (hB : ∀ n, 0 < n → ‖(hilbertSequence f n : ℂ)‖ ≤ B) :
    (∑' k : ℕ, mellinSecond s (k + 1) *
      mean (fun n => (hilbertSequence f n : ℂ)) (k + 1)) = s * paretoMellin f s := by
  let F : ℕ → ℂ := fun n => (hilbertSequence f n : ℂ)
  have hfirst := (hasSum_first_mellin_pairing f s hs).tendsto_sum_nat
  have hsecond := (bounded_second_pairing_summable s (by linarith) F B hB).hasSum.tendsto_sum_nat
  have hboundary := terminal_pairing_tendsto_zero s (by linarith) F B hB
  have he : (fun N => partialSum (fun n => mellinSecond s n * mean F n) N) =
      (fun N => partialSum (fun n => mellinFirst s n * F n) N -
        (N : ℂ) * mellinFirst s (N + 1) * mean F N) := by
    funext N
    have h := mellin_pairing_prefix s F N
    linear_combination -h
  change Tendsto (fun N => partialSum (fun n => mellinSecond s n * mean F n) N)
    atTop (𝓝 _) at hsecond
  rw [he] at hsecond
  exact tendsto_nhds_unique hsecond (by simpa only [sub_zero, partialSum, F] using hfirst.sub hboundary)

end RiemannResearch.Analysis.Cesaro

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro

/-- This constant is finite by the proved weighted dual summability theorem. -/
def conditionalMellinDualSquare (s : ℂ) : ℝ :=
  ∑' k : ℕ, ‖mellinSecond s (k + 1)‖ ^ 2 / conditionalWeight k

theorem conditionalMellinDualSquare_nonneg (s : ℂ) : 0 ≤ conditionalMellinDualSquare s :=
  tsum_nonneg (fun k => div_nonneg (sq_nonneg _) (conditionalWeight_pos k).le)

end RiemannResearch.RH.Pareto
