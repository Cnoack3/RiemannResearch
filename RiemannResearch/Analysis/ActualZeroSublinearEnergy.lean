/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ActualZeroCoshMass
import RiemannResearch.Analysis.ActualZeroFixedStripConcentration
import RiemannResearch.Analysis.ActualZeroCountUpper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Sublinear horizontal energy and relaxed actual zero-density requirements

Source for the classical density statement and reflection strategy:
Ford--Zaharescu, "On the distribution of imaginary parts of zeros of the
Riemann zeta function", Lemma 2 and equation (3.8),
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .
The relaxed count-to-moment deductions follow the user-directed research
calculation of 21 October 2026. No novelty claim is intended.

All counts preserve actual zeros, analytic multiplicity and strict/inclusive
boundary conventions. Existing Riemann--von Mangoldt supplies the total-count
upper bound. A single moving-strip count and its explicit head budget suffice
for the height-normalized ordinate bias; count-normalized qualitative
equidistribution alone does not give this stronger normalization.

Every fixed real logarithmic loss is allowed when the exponential rate is
positive. The analytic count estimate itself remains an explicit proposition.
This module proves the deductions; it does not prove a classical Selberg or
Ingham density provider or assume RH.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

def SublinearHorizontalEnergy : Prop :=
  Tendsto (fun T : ℝ => horizontalEnergy T / T) atTop (𝓝 0)

theorem tendsto_ordinate_landau_error_of_sublinear_horizontal
    (u : ℝ) (hE : SublinearHorizontalEnergy) :
    Tendsto (fun T : ℝ => (ordinateSum T u - landauSum T u) / (T : ℂ))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun T : ℝ =>
      (u ^ 2 * Real.exp (|u| / 2)) * (horizontalEnergy T / T))
      atTop (𝓝 0) := by
    simpa using hE.const_mul (u ^ 2 * Real.exp (|u| / 2))
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  calc
    _ ≤ ((u ^ 2 * Real.exp (|u| / 2)) * horizontalEnergy T) / T :=
      div_le_div_of_nonneg_right (ordinate_landau_error T u) hT.le
    _ = _ := by ring

theorem normalized_ordinate_landau_error_of_right_expTail_band
    (T u M decay θ : ℝ) (hT : 0 < T) (hM : 0 ≤ M)
    (hdecay : 0 < decay) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hu : |u| ≤ θ * decay)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ M * Real.exp (-decay * t)) :
    ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
      (2 * u ^ 2 / (1 - θ ^ 2)) * (M / (T * decay ^ 2)) := by
  have hu' : |u| < decay := by nlinarith [mul_pos (sub_pos.mpr hθ1) hdecay]
  have hθsq : 0 < 1 - θ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hθ1) (by linarith : 0 < 1 + θ)]
  have hbase : 0 < decay ^ 2 * (1 - θ ^ 2) := by positivity
  have hprod : 0 ≤ (θ * decay - |u|) * (θ * decay + |u|) :=
    mul_nonneg (by linarith) (by positivity)
  have hden : decay ^ 2 * (1 - θ ^ 2) ≤ decay ^ 2 - u ^ 2 := by
    nlinarith [hprod, sq_abs u]
  have hd : 0 < decay ^ 2 - u ^ 2 := lt_of_lt_of_le hbase hden
  have h := ordinate_landau_error_of_right_expTail T u M decay hM hu' htail
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  calc
    _ ≤ (2 * M * u ^ 2 / (decay ^ 2 - u ^ 2)) / T :=
      div_le_div_of_nonneg_right h hT.le
    _ ≤ (2 * M * u ^ 2 / (decay ^ 2 * (1 - θ ^ 2))) / T := by
      apply div_le_div_of_nonneg_right _ hT.le
      apply (div_le_div_iff₀ hd hbase).mpr
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by
      field_simp [ne_of_gt hT, ne_of_gt hdecay, ne_of_gt hθsq]

theorem tendsto_ordinate_landau_error_of_tailProfile
    (M decay : ℝ → ℝ)
    (hdecay : Tendsto decay atTop atTop)
    (hbudget : Tendsto (fun T : ℝ => M T / (T * (decay T) ^ 2)) atTop (𝓝 0))
    (htail : ∀ᶠ T : ℝ in atTop, 0 ≤ M T ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 2),
        rightStrictTail T t ≤ M T * Real.exp (-(decay T) * t))
    (u : ℝ) :
    Tendsto (fun T : ℝ => (ordinateSum T u - landauSum T u) / (T : ℂ))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun T : ℝ => (8 * u ^ 2 / 3) *
      (M T / (T * (decay T) ^ 2))) atTop (𝓝 0) := by
    simpa using hbudget.const_mul (8 * u ^ 2 / 3)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [htail, eventually_gt_atTop (0 : ℝ),
    hdecay.eventually_gt_atTop (2 * |u| + 1)] with T hd hT hdecayT
  have hdecay0 : 0 < decay T := by linarith [abs_nonneg u]
  have hu : |u| ≤ (1 / 2 : ℝ) * decay T := by linarith
  have h := normalized_ordinate_landau_error_of_right_expTail_band
    T u (M T) (decay T) (1 / 2) hT hd.1 hdecay0 (by norm_num) (by norm_num) hu hd.2
  convert h using 1 <;> ring


/-- A uniform inclusive count bound with arbitrary positive exponential rate
and arbitrary real logarithmic loss. This is an explicit analytic premise. -/
def UniformLogLossDensity (a b : ℝ) : Prop :=
  ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      rightInclusiveCount T σ ≤ C * T * (Real.log T) ^ b *
        Real.exp (-(a * Real.log T) * (σ - 1 / 2))

theorem uniformLogLossDensity_of_uniformSelberg (a : ℝ)
    (hD : UniformSelbergDensity a) : UniformLogLossDensity a 1 := by
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  refine ⟨C, T₀, hC, hT₀, fun T hT => ?_⟩
  have hTpos : 0 < T := by linarith
  simpa only [Real.rpow_one] using
    (selbergDensityBound_iff_exp T C a hTpos).mp (hD T hT)

theorem logLoss_tailProfile_budget (C a b : ℝ) (ha : 0 < a) (hb : b < 2) :
    Tendsto (fun T : ℝ =>
      (C * T * (Real.log T) ^ b) / (T * (a * Real.log T) ^ 2))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun T : ℝ => (C / a ^ 2) *
      (Real.log T) ^ (-(2 - b))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (show 0 < 2 - b by linarith)).comp
      Real.tendsto_log_atTop).const_mul (C / a ^ 2)
  apply hg.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hT0 : T ≠ 0 := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  rw [show -(2 - b) = b - 2 by ring, Real.rpow_sub hL,
    show (Real.log T) ^ (2 : ℝ) = (Real.log T) ^ 2 from Real.rpow_natCast _ 2]
  field_simp [hT0, ne_of_gt ha, ne_of_gt hL]

theorem rightTailProfile_of_uniformLogLossDensity (a b : ℝ)
    (hD : UniformLogLossDensity a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      0 ≤ C * T * (Real.log T) ^ b ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 2),
        rightStrictTail T t ≤ (C * T * (Real.log T) ^ b) *
          Real.exp (-(a * Real.log T) * t) := by
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have hT1 : 1 < T := lt_of_lt_of_le hT₀ hT
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  refine ⟨by positivity, ?_⟩
  intro t ht
  have hσ : 1 / 2 + t ∈ Icc (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have h := hD T hT (1 / 2 + t) hσ
  have heq : 1 / 2 + t - 1 / 2 = t := by ring
  rw [heq] at h
  exact (rightStrictTail_le_inclusive T t).trans h

theorem tendsto_ordinate_landau_error_of_logLossDensity_direct
    (a b : ℝ) (ha : 0 < a) (hb : b < 2)
    (hD : UniformLogLossDensity a b) (u : ℝ) :
    Tendsto (fun T : ℝ => (ordinateSum T u - landauSum T u) / (T : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, htail⟩ := rightTailProfile_of_uniformLogLossDensity a b hD
  exact tendsto_ordinate_landau_error_of_tailProfile
    (fun T => C * T * (Real.log T) ^ b) (fun T => a * Real.log T)
    (Filter.Tendsto.const_mul_atTop ha Real.tendsto_log_atTop)
    (logLoss_tailProfile_budget C a b ha hb) htail u

theorem horizontalEnergy_le_twice_coshTail (T : ℝ) :
    horizontalEnergy T ≤ 2 * badWeightedSum T 0 (fun t => Real.cosh t - 1) := by
  rw [badWeightedSum_eq_realSum]
  have heq : 2 * realSum T (fun ρ =>
      if 0 < |ρ.re - 1 / 2| then Real.cosh |ρ.re - 1 / 2| - 1 else 0) =
      realSum T (fun ρ =>
        (if 0 < |ρ.re - 1 / 2| then Real.cosh |ρ.re - 1 / 2| - 1 else 0) * 2) := by
    rw [realSum_mul_const, mul_comm]
  rw [heq]
  apply realSum_mono
  intro ρ hρ
  by_cases hd : ρ.re - 1 / 2 = 0
  · simp only [hd, abs_zero, lt_self_iff_false, ite_false, zero_mul, sq]
    norm_num
  · rw [if_pos (abs_pos.mpr hd)]
    have h := Real.sq_div_two_le_cosh_sub_one |ρ.re - 1 / 2|
    rw [sq_abs] at h
    linarith

theorem horizontalEnergy_le_of_right_expTail
    (T M decay : ℝ) (hM : 0 ≤ M) (hdecay : 1 < decay)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ M * Real.exp (-decay * t)) :
    horizontalEnergy T ≤ 4 * M / (decay ^ 2 - 1) := by
  have hfull : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T t ≤ (2 * M) * Real.exp (-decay * t) := by
    intro t ht
    rw [strictTail_eq_twice_right T t ht.1]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (htail t ht) (by norm_num : (0 : ℝ) ≤ 2)
  have hc := badCoshSum_le_of_expTail_closed T 0 1 (2 * M) decay
    (by norm_num) (by norm_num) (by norm_num) hdecay hfull
  have hr := coshTail_closed_le_rational 1 decay (by norm_num) hdecay
  norm_num only [mul_zero, Real.cosh_zero, sub_self, zero_mul, Real.exp_zero,
    zero_add, one_mul, abs_one, one_pow] at hc hr
  calc
    _ ≤ 2 * badWeightedSum T 0 (fun t => Real.cosh t - 1) :=
      horizontalEnergy_le_twice_coshTail T
    _ ≤ 2 * ((2 * M) * (1 / (decay ^ 2 - 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hc.trans (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by ring

theorem sublinearHorizontalEnergy_of_tailProfile (M decay : ℝ → ℝ)
    (hdecay : Tendsto decay atTop atTop)
    (hbudget : Tendsto (fun T : ℝ => M T / (T * (decay T) ^ 2)) atTop (𝓝 0))
    (htail : ∀ᶠ T : ℝ in atTop, 0 ≤ M T ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 2),
        rightStrictTail T t ≤ M T * Real.exp (-(decay T) * t)) :
    SublinearHorizontalEnergy := by
  have hg : Tendsto (fun T : ℝ => (16 / 3 : ℝ) *
      (M T / (T * (decay T) ^ 2))) atTop (𝓝 0) := by
    simpa using hbudget.const_mul (16 / 3 : ℝ)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [htail, eventually_gt_atTop (0 : ℝ),
    hdecay.eventually_gt_atTop 2] with T hd hT hq
  have hM : 0 ≤ M T := hd.1
  have hq0 : 0 < decay T := by linarith
  have hden : 0 < (decay T) ^ 2 - 1 := by nlinarith
  have hbase : 0 < (3 / 4 : ℝ) * (decay T) ^ 2 := by positivity
  have hle : (3 / 4 : ℝ) * (decay T) ^ 2 ≤ (decay T) ^ 2 - 1 := by
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (horizontalEnergy_nonneg T) hT.le)]
  calc
    _ ≤ (4 * M T / ((decay T) ^ 2 - 1)) / T :=
      div_le_div_of_nonneg_right
        (horizontalEnergy_le_of_right_expTail T (M T) (decay T) hd.1 (by linarith) hd.2)
        hT.le
    _ ≤ (4 * M T / ((3 / 4 : ℝ) * (decay T) ^ 2)) / T := by
      apply div_le_div_of_nonneg_right _ hT.le
      apply (div_le_div_iff₀ hden hbase).mpr
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by field_simp <;> ring

theorem sublinearHorizontalEnergy_of_logLossDensity_direct
    (a b : ℝ) (ha : 0 < a) (hb : b < 2)
    (hD : UniformLogLossDensity a b) : SublinearHorizontalEnergy := by
  obtain ⟨C, hC, htail⟩ := rightTailProfile_of_uniformLogLossDensity a b hD
  exact sublinearHorizontalEnergy_of_tailProfile
    (fun T => C * T * (Real.log T) ^ b) (fun T => a * Real.log T)
    (Filter.Tendsto.const_mul_atTop ha Real.tendsto_log_atTop)
    (logLoss_tailProfile_budget C a b ha hb) htail


/-- Only one moving strip needs an analytic count estimate. -/
theorem sublinearHorizontalEnergy_of_shrinkingStrip (δ : ℝ → ℝ)
    (hδ : ∀ᶠ T : ℝ in atTop, 0 ≤ δ T)
    (hhead : Tendsto (fun T : ℝ => (δ T) ^ 2 * Real.log T) atTop (𝓝 0))
    (htail : Tendsto (fun T : ℝ => strictTail T (δ T) / T) atTop (𝓝 0)) :
    SublinearHorizontalEnergy := by
  obtain ⟨C, hC, hcount⟩ := exists_count_le_height_log
  have hg : Tendsto (fun T : ℝ => C * ((δ T) ^ 2 * Real.log T) +
      (1 / 4 : ℝ) * (strictTail T (δ T) / T)) atTop (𝓝 0) := by
    simpa using (hhead.const_mul C).add (htail.const_mul (1 / 4 : ℝ))
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hδ, eventually_ge_atTop (9 : ℝ)] with T hd hT
  have hT0 : 0 < T := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (horizontalEnergy_nonneg T) hT0.le)]
  calc
    _ ≤ ((δ T) ^ 2 * (Zeta23.Ncount 0 T : ℝ) +
          (1 / 4 : ℝ) * strictTail T (δ T)) / T :=
      div_le_div_of_nonneg_right (horizontalEnergy_le_fixedStrip T (δ T) hd) hT0.le
    _ ≤ ((δ T) ^ 2 * (C * T * Real.log T) +
          (1 / 4 : ℝ) * strictTail T (δ T)) / T := by
      apply div_le_div_of_nonneg_right _ hT0.le
      exact add_le_add (mul_le_mul_of_nonneg_left (hcount T hT) (sq_nonneg _)) le_rfl
    _ = _ := by field_simp

private theorem loglog_pow_div_log_tendsto_zero (n : ℕ) :
    Tendsto (fun T : ℝ => (Real.log (Real.log T)) ^ n / Real.log T)
      atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT
  simp only [Function.comp_def, Real.exp_neg, Real.exp_log hT, div_eq_mul_inv]

/-- A loglog/log window with a margin absorbing every fixed log loss. -/
def logLossWindow (a b T : ℝ) : ℝ :=
  ((max b 0 + 2) / a) * Real.log (Real.log T) / Real.log T

theorem logLossWindow_tendsto_zero (a b : ℝ) :
    Tendsto (logLossWindow a b) atTop (𝓝 0) := by
  change Tendsto (fun T : ℝ =>
    ((max b 0 + 2) / a) * Real.log (Real.log T) / Real.log T) atTop (𝓝 0)
  simpa only [pow_one, mul_div_assoc, mul_zero] using
    (loglog_pow_div_log_tendsto_zero 1).const_mul ((max b 0 + 2) / a)

theorem logLossWindow_head_tendsto_zero (a b : ℝ) :
    Tendsto (fun T : ℝ => (logLossWindow a b T) ^ 2 * Real.log T)
      atTop (𝓝 0) := by
  have h : Tendsto (fun T : ℝ => (((max b 0 + 2) / a) ^ 2) *
      ((Real.log (Real.log T)) ^ 2 / Real.log T)) atTop (𝓝 0) := by
    simpa using (loglog_pow_div_log_tendsto_zero 2).const_mul
      (((max b 0 + 2) / a) ^ 2)
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT
  dsimp only [logLossWindow]
  field_simp

theorem eventually_logLossWindow_mem (a b : ℝ) (ha : 0 < a) :
    ∀ᶠ T : ℝ in atTop, logLossWindow a b T ∈ Icc (0 : ℝ) (1 / 2) := by
  have hs := (logLossWindow_tendsto_zero a b).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hs, Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT hL
  have hLL : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hL
  have hL0 : 0 < Real.log T := by linarith
  have hc : 0 < max b 0 + 2 := by linarith [le_max_right b 0]
  exact ⟨by dsimp only [logLossWindow]; positivity, hT.le⟩

theorem logLossWindow_tail_tendsto_zero (a b : ℝ) (ha : 0 < a)
    (hD : UniformLogLossDensity a b) :
    Tendsto (fun T : ℝ => strictTail T (logLossWindow a b T) / T)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, htail⟩ := rightTailProfile_of_uniformLogLossDensity a b hD
  let c : ℝ := max b 0 + 2
  have hcb : 0 < c - b := by
    dsimp only [c]
    linarith [le_max_left b 0]
  have hg : Tendsto (fun T : ℝ => (2 * C) * (Real.log T) ^ (b - c))
      atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop hcb).comp Real.tendsto_log_atTop).const_mul (2 * C)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [htail, eventually_logLossWindow_mem a b ha,
    eventually_gt_atTop (1 : ℝ)] with T hd hδ hT
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hexp : Real.exp (-(a * Real.log T) * logLossWindow a b T) =
      (Real.log T) ^ (-c) :=
    selberg_movingWindow_exp T a c hL (ne_of_gt ha)
  have hfull : strictTail T (logLossWindow a b T) ≤
      2 * ((C * T * (Real.log T) ^ b) *
        Real.exp (-(a * Real.log T) * logLossWindow a b T)) := by
    rw [strictTail_eq_twice_right T _ hδ.1]
    exact mul_le_mul_of_nonneg_left (hd.2 _ hδ) (by norm_num)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (strictTail_nonneg _ _) hT0.le)]
  calc
    _ ≤ (2 * ((C * T * (Real.log T) ^ b) *
        Real.exp (-(a * Real.log T) * logLossWindow a b T))) / T :=
      div_le_div_of_nonneg_right hfull hT0.le
    _ = (2 * C) * ((Real.log T) ^ b * (Real.log T) ^ (-c)) := by
      rw [hexp]
      field_simp
    _ = _ := by rw [← Real.rpow_add hL]; congr 2

/-- Every fixed real logarithmic loss is sufficient at height normalization.
The actual Riemann--von Mangoldt upper count controls the central strip. -/
theorem sublinearHorizontalEnergy_of_logLossDensity
    (a b : ℝ) (ha : 0 < a) (hD : UniformLogLossDensity a b) :
    SublinearHorizontalEnergy := by
  exact sublinearHorizontalEnergy_of_shrinkingStrip (logLossWindow a b)
    ((eventually_logLossWindow_mem a b ha).mono fun _ h => h.1)
    (logLossWindow_head_tendsto_zero a b)
    (logLossWindow_tail_tendsto_zero a b ha hD)

theorem tendsto_ordinate_landau_error_of_logLossDensity
    (a b : ℝ) (ha : 0 < a) (hD : UniformLogLossDensity a b) (u : ℝ) :
    Tendsto (fun T : ℝ => (ordinateSum T u - landauSum T u) / (T : ℂ))
      atTop (𝓝 0) :=
  tendsto_ordinate_landau_error_of_sublinear_horizontal u
    (sublinearHorizontalEnergy_of_logLossDensity a b ha hD)


/-- The original Selberg premise supplies the weaker energy input for every
positive exponent, with no distinguished one-quarter constant. -/
theorem sublinearHorizontalEnergy_of_uniformSelberg (a : ℝ) (ha : 0 < a)
    (hD : UniformSelbergDensity a) : SublinearHorizontalEnergy :=
  sublinearHorizontalEnergy_of_logLossDensity a 1 ha
    (uniformLogLossDensity_of_uniformSelberg a hD)

/-- One moving inclusive right-half count is enough; reflection retains
threshold copies and all analytic multiplicities. -/
theorem sublinearHorizontalEnergy_of_shrinkingInclusiveCount (δ : ℝ → ℝ)
    (hδ : ∀ᶠ T : ℝ in atTop, 0 ≤ δ T)
    (hhead : Tendsto (fun T : ℝ => (δ T) ^ 2 * Real.log T) atTop (𝓝 0))
    (hright : Tendsto (fun T : ℝ =>
      rightInclusiveCount T (1 / 2 + δ T) / T) atTop (𝓝 0)) :
    SublinearHorizontalEnergy := by
  apply sublinearHorizontalEnergy_of_shrinkingStrip δ hδ hhead
  have hg : Tendsto (fun T : ℝ =>
      2 * (rightInclusiveCount T (1 / 2 + δ T) / T)) atTop (𝓝 0) := by
    simpa using hright.const_mul 2
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hδ, eventually_gt_atTop (0 : ℝ)] with T hd hT
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (strictTail_nonneg _ _) hT.le)]
  calc
    _ ≤ (2 * rightInclusiveCount T (1 / 2 + δ T)) / T :=
      div_le_div_of_nonneg_right (strictTail_le_twice_inclusive T (δ T) hd) hT.le
    _ = _ := by ring

end RiemannResearch.Analysis.ActualZeroOrdinate
