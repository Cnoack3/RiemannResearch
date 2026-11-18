/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryCentralPeak
import RiemannResearch.Analysis.MontgomeryFejerResolution
import RiemannResearch.Analysis.MontgomeryGaussianSmoothing
import RiemannResearch.Analysis.MontgomeryTransitionFrequency
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform central Fourier estimates for varying Fejér radii

The central profile uses the corrected positive-cutoff input of
Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh, arXiv:2501.14545v3, (3.5).
The exact triangle-weight correction is its first absolute Fourier moment.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryHorizontalBessel

/-- The first absolute moment of the central band in the frequency coordinate. -/
def centralFourierAbsMoment (T : ℝ) : ℝ :=
  ∫ α in (-centralFourierRadius T)..centralFourierRadius T, |α| * formFactor T α

theorem mul_fejerCentralContribution_eq_mass_sub_moment (T : ℝ) {R : ℝ} (hR : 0 < R) :
    R * fejerCentralContribution T R =
      (∫ α in (-centralFourierRadius T)..centralFourierRadius T, formFactor T α) -
        centralFourierAbsMoment T / R := by
  let b := centralFourierRadius T
  have hF := MontgomeryGaussianSmoothing.continuous_formFactor T
  have hα : Continuous (fun α : ℝ => |α| * formFactor T α) := continuous_abs.mul hF
  have hW : Continuous (fun α : ℝ => (1 / R) * (|α| * formFactor T α)) :=
    hα.const_mul _
  have hrewrite (α : ℝ) : (1 - |α| / R) * formFactor T α =
      formFactor T α - (1 / R) * (|α| * formFactor T α) := by ring
  unfold fejerCentralContribution centralFourierAbsMoment
  simp_rw [hrewrite]
  rw [intervalIntegral.integral_sub (hF.intervalIntegrable (-b) b)
    (hW.intervalIntegrable (-b) b), intervalIntegral.integral_const_mul]
  field_simp [hR.ne']
  rfl

theorem centralFourierAbsMoment_bounds {T : ℝ} (hT : 1 < T)
    (hb : 0 ≤ centralFourierRadius T) :
    0 ≤ centralFourierAbsMoment T ∧ centralFourierAbsMoment T ≤
      centralFourierRadius T *
        (∫ α in (-centralFourierRadius T)..centralFourierRadius T, formFactor T α) := by
  let b := centralFourierRadius T
  have horder : -b ≤ b := by change 0 ≤ b at hb; linarith only [hb]
  have hF := MontgomeryGaussianSmoothing.continuous_formFactor T
  have hα : Continuous (fun α : ℝ => |α| * formFactor T α) := continuous_abs.mul hF
  unfold centralFourierAbsMoment
  refine ⟨intervalIntegral.integral_nonneg horder
    (fun α _ => mul_nonneg (abs_nonneg α) (formFactor_nonneg hT α)), ?_⟩
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on horder (hα.intervalIntegrable (-b) b)
    ((hF.const_mul b).intervalIntegrable (-b) b)
  intro α hαb
  exact mul_le_mul_of_nonneg_right (abs_le.mpr hαb) (formFactor_nonneg hT α)

/-- The central mass estimate holds uniformly over every Fejér radius at least one. -/
theorem eventually_fejer_central_scaled_error (h : BGSTBPositiveCutoffEstimate) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 1 ≤ R →
      |R * fejerCentralContribution T R - 1| ≤ K * centralFourierRadius T := by
  obtain ⟨C, hC, hmass⟩ := eventually_raw_central_mass_error h
  refine ⟨C + 2, by positivity, ?_⟩
  have hm2 := (raw_central_mass_tendsto_one h).eventually
    (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hmass, hm2, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0]
    with T hmass' hm2' hT hlog
  intro R hR
  let b := centralFourierRadius T
  let M := ∫ α in (-b)..b, formFactor T α
  change |M - 1| ≤ C * b at hmass'
  change M < 2 at hm2'
  have hb : 0 ≤ b := div_nonneg hlog (Real.log_pos hT).le
  have hR0 := zero_lt_one.trans_le hR
  obtain ⟨hj0, hj⟩ := centralFourierAbsMoment_bounds hT hb
  have hbound : centralFourierAbsMoment T / R ≤ 2 * b := calc
    _ ≤ centralFourierAbsMoment T :=
      (div_le_iff₀ hR0).mpr (le_mul_of_one_le_right hj0 hR)
    _ ≤ b * M := hj
    _ ≤ b * 2 := mul_le_mul_of_nonneg_left hm2'.le hb
    _ = _ := mul_comm _ _
  rw [mul_fejerCentralContribution_eq_mass_sub_moment T hR0]
  change |(M - centralFourierAbsMoment T / R) - 1| ≤ (C + 2) * b
  calc
    _ = |(M - 1) - centralFourierAbsMoment T / R| := by congr 1; ring
    _ ≤ |M - 1| + |centralFourierAbsMoment T / R| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (M - 1) (-(centralFourierAbsMoment T / R))
    _ ≤ _ := by
      rw [abs_of_nonneg (div_nonneg hj0 hR0.le)]
      nlinarith only [hmass', hbound]

/-- The rate for the unscaled core tends to zero uniformly, including on moving radii. -/
theorem eventually_fejer_central_error (h : BGSTBPositiveCutoffEstimate) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 1 ≤ R →
      |fejerCentralContribution T R - 1 / R| ≤ K * centralFourierRadius T / R := by
  obtain ⟨K, hK, hb⟩ := eventually_fejer_central_scaled_error h
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb] with T hT
  intro R hR
  have hR0 := zero_lt_one.trans_le hR
  have he : R * (fejerCentralContribution T R - 1 / R) = R * fejerCentralContribution T R - 1 := by
    field_simp [hR0.ne']
  have hu := hT R hR
  rw [← he, abs_mul, abs_of_pos hR0, mul_comm R] at hu
  exact (le_div_iff₀ hR0).mpr hu

/-- The outside statistic with the central model restored gives an absolute
cutoff certificate when the central approximation costs at most one quarter of a pair. -/
theorem eventually_outside_fejer_critical_line_iff (h : BGSTBPositiveCutoffEstimate) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 1 ≤ R →
      fejerResolvingRadius T ≤ R →
      (T * Real.log T / (2 * Real.pi)) * (K * centralFourierRadius T / R) ≤ 1 / 4 →
      ((T * Real.log T / (2 * Real.pi)) * (fejerOutsideCentral T R + 1 / R) -
        (analyticPairCount T : ℝ) < 3 / 2 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2) := by
  obtain ⟨K, hK, hb⟩ := eventually_fejer_central_error h
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T ht hT
  intro R hR hresolve hquarter
  let D := T * Real.log T / (2 * Real.pi)
  have hD : 0 ≤ D := (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT))
    (by positivity)).le
  have hadd := (abs_le.mp (ht R hR))
  have hlow := (mul_le_mul_of_nonneg_left hadd.1 hD)
  have hupp := (mul_le_mul_of_nonneg_left hadd.2 hD)
  change D * (K * centralFourierRadius T / R) ≤ 1 / 4 at hquarter
  have herr : -(1 / 4 : ℝ) ≤ D * (fejerCentralContribution T R - 1 / R) ∧
      D * (fejerCentralContribution T R - 1 / R) ≤ 1 / 4 := by
    rw [mul_neg] at hlow
    exact ⟨(neg_le_neg hquarter).trans hlow, hupp.trans hquarter⟩
  have hband := normalized_fejer_sub_analytic_in_collision_unit_interval hT hresolve
  dsimp only at hband
  let A : ℝ := analyticPairCount T
  change (distinctZeroCollision T : ℝ) ≤ D * fejerFormFactor T R - A ∧
    D * fejerFormFactor T R - A < (distinctZeroCollision T : ℝ) + 1 at hband
  change (D * (fejerOutsideCentral T R + 1 / R) - A < 3 / 2) ↔ _
  have heq : D * (fejerOutsideCentral T R + 1 / R) - A =
      D * fejerFormFactor T R - A -
        D * (fejerCentralContribution T R - 1 / R) := by unfold fejerOutsideCentral; ring
  rw [heq]
  constructor
  · intro hsmall ρ hρ
    by_contra hoff
    have htwo : (2 : ℝ) ≤ distinctZeroCollision T := by
      exact_mod_cast two_le_distinctZeroCollision_of_off_line hρ hoff
    linarith only [hsmall, htwo, hband.1, herr.2]
  · intro hall
    have hc := (collision_eq_analyticPairCount_iff T).mpr hall
    have hz : distinctZeroCollision T = 0 := by
      have he := collision_eq_analytic_add_distinctZeroCollision T
      omega
    have hbelow := hband.2
    rw [hz, Nat.cast_zero, zero_add] at hbelow
    linarith only [hbelow, herr.1]

end RiemannResearch.Analysis.MontgomeryFormFactor
