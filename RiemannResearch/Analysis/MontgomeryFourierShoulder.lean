/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryCentralPeak
import RiemannResearch.Analysis.MontgomeryGaussianSmoothing
import RiemannResearch.Analysis.MontgomeryHorizontalPairing
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryLoglogTransfer
import RiemannResearch.Analysis.MontgomeryTransitionFrequency
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Negligible raw Fourier mass up to inverse square-root log frequency

On the positive band between the central core and `(log T)^{-1/2}`, combine
the corrected BGSTB estimate (arXiv:2501.14545v3, (3.5)) with the unconditional
square-root transfer. The negative band has the same mass by evenness.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate MontgomeryHorizontalBessel MontgomeryHorizontalTransfer

/-- The outer edge of the small-frequency band, equal to `(log T)⁻¹ᐟ²` for `T > 1`. -/
def shoulderFourierRadius (T : ℝ) : ℝ := Real.sqrt (Real.log T) / Real.log T

theorem eventually_shoulder_formFactor_bound (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      1 < T ∧ 0 ≤ centralFourierRadius T ∧
      centralFourierRadius T ≤ shoulderFourierRadius T ∧
      ∀ α ∈ Icc (centralFourierRadius T) (shoulderFourierRadius T),
        formFactor T α ≤ C * (1 + Real.log (Real.log T) ^ 2) := by
  obtain ⟨A, hA, hcomplex⟩ := sharpFormFactor_bound_of_bgstb h
  obtain ⟨K, hK, htransfer⟩ := eventually_sqrt_formFactor_difference_loglog_band
  refine ⟨4 + 4 * A + 4 * K ^ 2, by positivity, ?_⟩
  filter_upwards [hcomplex, htransfer, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
    (loglog_pow_div_log_tendsto_zero 2).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 1024)] with T hc ht hT hL1 hℓ hsmall
  let L := Real.log T
  let ℓ := Real.log L
  change 1 ≤ L at hL1
  change 0 < ℓ at hℓ
  change ℓ ^ 2 / L ≤ 1 / 1024 at hsmall
  have hL : 0 < L := Real.log_pos hT
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hroot1 : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL1
  have hrootSq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  have h32 : 32 * ℓ ≤ Real.sqrt L := by
    apply (sq_le_sq₀ (by positivity) hroot.le).mp
    rw [hrootSq]
    have hh := (div_le_iff₀ hL).mp hsmall
    nlinarith only [hh]
  have hband : Real.sqrt L ≤ horizontalTailDecay T / 4 := by
    change Real.sqrt L ≤ L / (8 * ℓ) / 4
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4),
      le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hℓ)]
    calc
      _ = Real.sqrt L * (32 * ℓ) := by ring
      _ ≤ Real.sqrt L * Real.sqrt L := mul_le_mul_of_nonneg_left h32 hroot.le
      _ = L := Real.mul_self_sqrt hL.le
  have hb0 : 0 ≤ centralFourierRadius T := div_nonneg hℓ.le hL.le
  have hb : centralFourierRadius T ≤ shoulderFourierRadius T :=
    div_le_div_of_nonneg_right (by linarith only [h32, hℓ]) hL.le
  refine ⟨hT, hb0, hb, ?_⟩
  intro α hα
  let u := α * L
  have hu0 : ℓ ≤ u := (div_le_iff₀ hL).mp hα.1
  have hu1 : u ≤ Real.sqrt L := (le_div_iff₀ hL).mp hα.2
  have hu2 : u ^ 2 ≤ L := by
    rw [← hrootSq]
    exact (sq_le_sq₀ (hℓ.le.trans hu0) hroot.le).mpr hu1
  have hα0 : 0 ≤ α := hb0.trans hα.1
  have hα1 : α ≤ 1 := hα.2.trans ((div_le_iff₀ hL).mpr (by
    rw [one_mul]
    calc
      Real.sqrt L ≤ Real.sqrt L * Real.sqrt L := le_mul_of_one_le_right hroot.le hroot1
      _ = L := Real.mul_self_sqrt hL.le))
  have hq : Real.exp (-2 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hℓ, hu0])
  have hpeak : Real.exp (-2 * u) * L ≤ 1 := calc
    _ ≤ Real.exp (-ℓ) * L := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith only [hu0, hℓ])) hL.le
    _ = 1 := by rw [Real.exp_neg, Real.exp_log hL, inv_mul_cancel₀ hL.ne']
  have hinv : 1 / Real.sqrt L ≤ 1 := (div_le_iff₀ hroot).mpr (by simpa using hroot1)
  let s := sharpFormFactor T α
  let f := formFactor T α
  have hs0 : 0 ≤ s := MontgomeryHorizontalPairing.sharpFormFactor_nonneg hT α
  have hf0 : 0 ≤ f := formFactor_nonneg hT α
  have hs : s ≤ 2 + 2 * A := by
    have h' := (abs_le.mp (hc α ⟨hα0, hα1⟩)).2
    change s - (Real.exp (-2 * u) * L + α) ≤ A * (Real.exp (-2 * u) + 1 / Real.sqrt L) at h'
    have he := mul_le_mul_of_nonneg_left (add_le_add hq hinv) hA
    linarith only [h', he, hpeak, hα1]
  let B := (1 + u ^ 2) * horizontalLogRate T
  have hB0 : 0 ≤ B := by dsimp [B, horizontalLogRate]; positivity
  have hB : B ≤ 2 * ℓ ^ 2 := calc
    _ ≤ (2 * L) * (ℓ ^ 2 / L) := mul_le_mul_of_nonneg_right
      (by linarith only [hL1, hu2]) (by positivity)
    _ = _ := by field_simp [hL.ne']
  have htransfer' : |Real.sqrt s - Real.sqrt f| ≤ K * Real.sqrt B :=
    ht α ((abs_of_nonneg (mul_nonneg hα0 hL.le)).trans_le (hu1.trans hband))
  let e := K * Real.sqrt B
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hfsqrt : Real.sqrt f ≤ Real.sqrt s + e := by
    change |Real.sqrt s - Real.sqrt f| ≤ e at htransfer'
    linarith only [(abs_le.mp htransfer').1]
  have hfsq := (sq_le_sq₀ (Real.sqrt_nonneg f) (add_nonneg (Real.sqrt_nonneg s) he0)).mpr hfsqrt
  rw [Real.sq_sqrt hf0] at hfsq
  have hsq : (Real.sqrt s + e) ^ 2 ≤ 2 * s + 2 * e ^ 2 := by
    nlinarith only [sq_nonneg (Real.sqrt s - e), Real.sq_sqrt hs0]
  have hesq : e ^ 2 ≤ K ^ 2 * (2 * ℓ ^ 2) := by
    dsimp [e]
    rw [mul_pow, Real.sq_sqrt hB0]
    exact mul_le_mul_of_nonneg_left hB (sq_nonneg K)
  change f ≤ (4 + 4 * A + 4 * K ^ 2) * (1 + ℓ ^ 2)
  have hKℓ : 0 ≤ (4 + 4 * A) * ℓ ^ 2 := by positivity
  nlinarith only [hfsq, hsq, hs, hesq, hKℓ, sq_nonneg K]

/-- Integrating the shoulder costs at most its length times the uniform logarithmic bound. -/
theorem eventually_positive_fourier_shoulder_mass_bound (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      let b := centralFourierRadius T
      let r := shoulderFourierRadius T
      0 ≤ (∫ α in b..r, formFactor T α) ∧
        (∫ α in b..r, formFactor T α) ≤ C * (1 + Real.log (Real.log T) ^ 2) * r := by
  obtain ⟨C, hC, hbound⟩ := eventually_shoulder_formFactor_bound h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with T hT
  obtain ⟨hT, hb0, horder, hpoint⟩ := hT
  let b := centralFourierRadius T
  let r := shoulderFourierRadius T
  let M := C * (1 + Real.log (Real.log T) ^ 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨intervalIntegral.integral_nonneg_of_forall horder (formFactor_nonneg hT), ?_⟩
  have hF := MontgomeryGaussianSmoothing.continuous_formFactor T
  have hi := intervalIntegral.integral_mono_on horder (hF.intervalIntegrable b r)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume b r) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  change (∫ α in b..r, formFactor T α) ≤ M * r
  exact hi.trans ((mul_le_mul_of_nonneg_right (sub_le_self r hb0) hM).trans_eq (mul_comm _ _))

theorem positive_fourier_shoulder_mass_tendsto_zero (h : BGSTBPositiveCutoffEstimate) :
    Tendsto (fun T : ℝ =>
      ∫ α in centralFourierRadius T..shoulderFourierRadius T, formFactor T α) atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := eventually_positive_fourier_shoulder_mass_bound h
  have h1 : Tendsto shoulderFourierRadius atTop (𝓝 0) := by
    have h1' : Tendsto (fun T : ℝ => Real.sqrt (1 / Real.log T)) atTop (𝓝 0) := by
      simpa only [pow_zero, Real.sqrt_zero] using (loglog_pow_div_log_tendsto_zero 0).sqrt
    apply h1'.congr
    intro T
    rw [shoulderFourierRadius, Real.sqrt_div_self', Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
      Real.sqrt_one]
  have h2 : Tendsto (fun T : ℝ => Real.log (Real.log T) ^ 2 * shoulderFourierRadius T)
      atTop (𝓝 0) := by
    have h2' : Tendsto (fun T : ℝ => Real.sqrt (Real.log (Real.log T) ^ 4 / Real.log T))
        atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero] using (loglog_pow_div_log_tendsto_zero 4).sqrt
    apply h2'.congr
    intro T
    rw [shoulderFourierRadius, Real.sqrt_div_self',
      show Real.log (Real.log T) ^ 4 = (Real.log (Real.log T) ^ 2) ^ 2 by ring,
      Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (sq_nonneg _), mul_one_div]
  have hsum := (h1.add h2).const_mul C
  simp only [add_zero, mul_zero] at hsum
  refine squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2) ?_
  exact hsum.congr (fun _ => by ring)

end RiemannResearch.Analysis.MontgomeryFormFactor
