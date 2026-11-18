/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryCentralPeak
import RiemannResearch.Analysis.MontgomeryGaussianSmoothing
import RiemannResearch.Analysis.MontgomeryHorizontalPairing
import RiemannResearch.Analysis.MontgomeryLoglogTransfer
import RiemannResearch.Analysis.MontgomeryTransitionFrequency
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The extended small-frequency band of the raw Montgomery form factor

The complex form-factor input is Baluyot, Goldston, Suriajaya and
Turnage-Butterbaugh, arXiv:2501.14545v3, equation (3.5). The horizontal
comparison can grow pointwise across the band. Integrating its quadratic
majorant gives a cubic error in the band radius, which allows a wider band.
-/

noncomputable section
open Filter MeasureTheory Set intervalIntegral Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryHorizontalTransfer
open MontgomeryHorizontalBessel

theorem eventually_formFactor_le_on_shoulder (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      1 < T ∧ 0 ≤ centralFourierRadius T ∧
      ∀ α : ℝ, centralFourierRadius T ≤ α → α ≤ 1 →
        α * Real.log T ≤ horizontalTailDecay T / 4 →
        formFactor T α ≤ C * (1 + α ^ 2 * Real.log T * Real.log (Real.log T) ^ 2) := by
  obtain ⟨A, hA, hc⟩ := sharpFormFactor_bound_of_bgstb h
  obtain ⟨K, hK, hk⟩ := MontgomeryHorizontalBessel.eventually_sqrt_formFactor_difference_loglog_band
  let C := 4 + 4 * A + 2 * K ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hc, hk, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0,
    horizontalLogRate_tendsto_zero.eventually_le_const zero_lt_one] with T hc hk hT hL1 hℓ hrate
  let L := Real.log T
  let ℓ := Real.log L
  change 0 ≤ ℓ at hℓ
  have hL : 0 < L := Real.log_pos hT
  have hb : 0 ≤ centralFourierRadius T := div_nonneg hℓ hL.le
  refine ⟨hT, hb, fun α hα hα1 hband => ?_⟩
  let u := α * L
  let s := sharpFormFactor T α
  let f := formFactor T α
  have hα0 : 0 ≤ α := hb.trans hα
  have hu : ℓ ≤ u := (div_le_iff₀ hL).mp hα
  have hq : Real.exp (-2 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hu, hℓ])
  have hpeak : Real.exp (-2 * u) * L ≤ 1 := calc
    _ ≤ Real.exp (-ℓ) * L := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith only [hu, hℓ])) hL.le
    _ = 1 := by rw [Real.exp_neg, Real.exp_log hL, inv_mul_cancel₀ hL.ne']
  have hroot : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL1
  have hinv : 1 / Real.sqrt L ≤ 1 := (div_le_iff₀ (Real.sqrt_pos.2 hL)).mpr (by simpa)
  have hs : s ≤ 2 + 2 * A := by
    have hv := (abs_le.mp (hc α ⟨hα0, hα1⟩)).2
    change s - (Real.exp (-2 * u) * L + α) ≤ A * (Real.exp (-2 * u) + 1 / Real.sqrt L) at hv
    have he := mul_le_mul_of_nonneg_left (add_le_add hq hinv) hA
    linarith only [hv, he, hpeak, hα1]
  let B := (1 + u ^ 2) * horizontalLogRate T
  have hB : 0 ≤ B := by dsimp [B, horizontalLogRate]; positivity
  let e := K * Real.sqrt B
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hcomp : |Real.sqrt s - Real.sqrt f| ≤ e :=
    hk α ((abs_of_nonneg (mul_nonneg hα0 hL.le)).trans_le hband)
  have hfs : Real.sqrt f ≤ Real.sqrt s + e := by
    linarith only [(abs_le.mp hcomp).1]
  have hfsq := (sq_le_sq₀ (Real.sqrt_nonneg f) (add_nonneg (Real.sqrt_nonneg s) he)).mpr hfs
  have hf0 : 0 ≤ f := formFactor_nonneg hT α
  rw [Real.sq_sqrt hf0] at hfsq
  have hsq : (Real.sqrt s + e) ^ 2 ≤ 2 * s + 2 * e ^ 2 := by
    have hs0 : 0 ≤ s := MontgomeryHorizontalPairing.sharpFormFactor_nonneg hT α
    nlinarith only [sq_nonneg (Real.sqrt s - e), Real.sq_sqrt hs0]
  have hBmajor : B ≤ 1 + α ^ 2 * L * ℓ ^ 2 := by
    have hBeq : B = horizontalLogRate T + α ^ 2 * L * ℓ ^ 2 := by
      change (1 + (α * L) ^ 2) * (ℓ ^ 2 / L) = ℓ ^ 2 / L + α ^ 2 * L * ℓ ^ 2
      field_simp [hL.ne'] <;> ring
    rw [hBeq]
    linarith only [hrate]
  have heSq : e ^ 2 = K ^ 2 * B := by dsimp [e]; rw [mul_pow, Real.sq_sqrt hB]
  have hBmul := mul_le_mul_of_nonneg_left hBmajor (show 0 ≤ 2 * K ^ 2 by positivity)
  have hCmul := mul_le_mul_of_nonneg_right (show 2 * K ^ 2 ≤ C by dsimp [C]; linarith)
    (show 0 ≤ α ^ 2 * L * ℓ ^ 2 by positivity)
  change f ≤ C * (1 + α ^ 2 * L * ℓ ^ 2)
  dsimp only [C] at hCmul ⊢
  nlinarith only [hfsq, hsq, heSq, hBmul, hCmul, hs]

/-- Integrating the uniform shoulder majorant costs a cubic term in the
moving frequency radius. -/
theorem eventually_positive_fourier_band_mass_le (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      let b := centralFourierRadius T
      1 < T ∧ 0 ≤ b ∧ ∀ r : ℝ, b ≤ r → r ≤ 1 →
        r * Real.log T ≤ horizontalTailDecay T / 4 →
        0 ≤ (∫ α in b..r, formFactor T α) ∧
          (∫ α in b..r, formFactor T α) ≤
            C * ((r - b) + Real.log T * Real.log (Real.log T) ^ 2 * ((r ^ 3 - b ^ 3) / 3)) ∧
          (∫ α in b..r, formFactor T α) ≤
            C * (r + r ^ 3 * Real.log T * Real.log (Real.log T) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := eventually_formFactor_le_on_shoulder h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with T ht
  obtain ⟨hT, hb0, ht⟩ := ht
  refine ⟨hT, hb0, fun r hr hr1 hrband => ?_⟩
  let b := centralFourierRadius T
  let L := Real.log T
  let ℓ := Real.log L
  let p : ℝ → ℝ := fun α => α ^ 2 * L * ℓ ^ 2
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hL : 0 < L := Real.log_pos hT
  have hmajor : Continuous (fun α : ℝ => C * (1 + p α)) :=
    (continuous_const.add hp).const_mul C
  have hI : (∫ α in b..r, formFactor T α) ≤ ∫ α in b..r, C * (1 + p α) :=
    intervalIntegral.integral_mono_on hr
      ((MontgomeryGaussianSmoothing.continuous_formFactor T).intervalIntegrable b r)
      (hmajor.intervalIntegrable b r)
      (fun α (hα : α ∈ Icc b r) =>
        ht α hα.1 (hα.2.trans hr1) ((mul_le_mul_of_nonneg_right hα.2 hL.le).trans hrband))
  have hIp : (∫ α in b..r, p α) = L * ℓ ^ 2 * ((r ^ 3 - b ^ 3) / 3) := by
    dsimp only [p]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, integral_pow]
    norm_num
    ring
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume b r := intervalIntegrable_const
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hconst (hp.intervalIntegrable b r),
    intervalIntegral.integral_const, smul_eq_mul, mul_one, hIp] at hI
  refine ⟨intervalIntegral.integral_nonneg_of_forall hr (formFactor_nonneg hT), hI, hI.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  have hr0 : 0 ≤ r := hb0.trans hr
  have hcub : (r ^ 3 - b ^ 3) / 3 ≤ r ^ 3 := by
    linarith only [pow_nonneg hr0 3, pow_nonneg hb0 3]
  calc
    _ ≤ r + L * ℓ ^ 2 * r ^ 3 :=
      add_le_add (sub_le_self r hb0) (mul_le_mul_of_nonneg_left hcub (by positivity))
    _ = _ := by ring

/-- In logarithmic notation the new edge is L⁻¹ᐟ³/(1 + log L). -/
def extendedShoulderRadius (T : ℝ) : ℝ :=
  (1 / Real.log T) ^ (1 / 3 : ℝ) / (1 + Real.log (Real.log T))

private theorem le_of_cube_le_cube {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 3 ≤ b ^ 3) :
    a ≤ b := by
  by_contra! hab
  have ha' := hb.trans_lt hab
  have hp := mul_pos (sub_pos.mpr hab) (show 0 < a ^ 2 + a * b + b ^ 2 by positivity)
  nlinarith only [hp, h]

theorem eventually_extendedShoulderRadius_band :
    ∀ᶠ T : ℝ in atTop,
      let L := Real.log T
      let ℓ := Real.log L
      let r := extendedShoulderRadius T
      1 < T ∧ 0 ≤ centralFourierRadius T ∧ centralFourierRadius T ≤ r ∧ r ≤ 1 ∧
        r * L ≤ horizontalTailDecay T / 4 ∧
        r + r ^ 3 * L * ℓ ^ 2 ≤ 2 / (1 + ℓ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 32768,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    (loglog_pow_div_log_tendsto_zero 6).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 8)] with T hT hlarge hℓ1 hsmall
  let L := Real.log T
  let ℓ := Real.log L
  let q := (1 / L) ^ (1 / 3 : ℝ)
  let e := 1 + ℓ
  let r := extendedShoulderRadius T
  change 32768 ≤ L at hlarge
  change 1 ≤ ℓ at hℓ1
  change ℓ ^ 6 / L ≤ 1 / 8 at hsmall
  have hL : 0 < L := Real.log_pos hT
  have hℓ : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have he : 0 < e := by dsimp [e]; positivity
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hpow : q ^ 3 = 1 / L := by
    dsimp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ 1 / L by positivity)]
    norm_num
  have hq : q ≤ 1 / 32 := by
    apply le_of_cube_le_cube (by norm_num)
    rw [hpow]
    exact (div_le_iff₀ hL).mpr (by linarith only [hlarge])
  have hL1 : 1 ≤ L := by linarith only [hlarge]
  have hr : r = q / e := rfl
  have hrle : r ≤ 1 / e := by
    rw [hr]
    exact div_le_div_of_nonneg_right (hq.trans (by norm_num)) he.le
  have hr1 : r ≤ 1 := hrle.trans ((div_le_iff₀ he).mpr (by dsimp [e]; linarith only [hℓ]))
  have hb0 : 0 ≤ centralFourierRadius T := div_nonneg hℓ.le hL.le
  have hb : centralFourierRadius T ≤ r := by
    rw [hr]
    change ℓ / L ≤ q / e
    apply (div_le_div_iff₀ hL he).mpr
    apply le_of_cube_le_cube (by positivity)
    have hl := mul_le_mul_of_nonneg_left hℓ1 hℓ.le
    have hℓe : ℓ * e ≤ 2 * ℓ ^ 2 := by dsimp [e]; nlinarith only [hl]
    have hqL : (q * L) ^ 3 = L ^ 2 := by
      rw [mul_pow, hpow]
      field_simp [hL.ne']
    calc
      (ℓ * e) ^ 3 ≤ (2 * ℓ ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hℓe 3
      _ = 8 * ℓ ^ 6 := by ring
      _ ≤ L := by linarith only [(div_le_iff₀ hL).mp hsmall]
      _ ≤ L ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hL1 hL.le]
      _ = (q * L) ^ 3 := hqL.symm
  have hr32 : r * (32 * ℓ) ≤ 1 := calc
    _ = q * (32 * ℓ) / e := by rw [hr]; ring
    _ ≤ (1 / 32) * (32 * ℓ) / e := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hq (by positivity)) he.le
    _ ≤ 1 := (div_le_iff₀ he).mpr (by dsimp [e]; linarith)
  have hz : r * L ≤ horizontalTailDecay T / 4 := by
    change r * L ≤ L / (8 * ℓ) / 4
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * ℓ)).mpr
    calc
      _ = (r * (32 * ℓ)) * L := by ring
      _ ≤ 1 * L := mul_le_mul_of_nonneg_right hr32 hL.le
      _ = _ := one_mul _
  have hc : r ^ 3 * L * ℓ ^ 2 ≤ 1 / e := by
    have hratio : r ^ 3 * L * ℓ ^ 2 = ℓ ^ 2 / e ^ 3 := by
      rw [hr, div_pow, hpow]
      field_simp [hL.ne', he.ne']
    rw [hratio]
    calc
      _ ≤ e ^ 2 / e ^ 3 := div_le_div_of_nonneg_right
        ((sq_le_sq₀ hℓ.le he.le).mpr (by dsimp [e]; linarith)) (by positivity)
      _ = _ := by field_simp [he.ne']
  refine ⟨hT, hb0, hb, hr1, hz, ?_⟩
  change r + r ^ 3 * L * ℓ ^ 2 ≤ 2 / e
  linarith only [hrle, hc, show (2 : ℝ) / e = 1 / e + 1 / e by ring]

theorem eventually_positive_extended_shoulder_mass_le (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      let b := centralFourierRadius T
      let r := extendedShoulderRadius T
      1 < T ∧ 0 ≤ b ∧ b ≤ r ∧ r ≤ 1 ∧
        0 ≤ (∫ α in b..r, formFactor T α) ∧
        (∫ α in b..r, formFactor T α) ≤ C / (1 + Real.log (Real.log T)) := by
  obtain ⟨C, hC, hm⟩ := eventually_positive_fourier_band_mass_le h
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hm, eventually_extendedShoulderRadius_band] with T hm hr
  obtain ⟨hT, h0, hbr, hr1, hband, hrate⟩ := hr
  obtain ⟨hlo, _, hhi⟩ := hm.2.2 _ hbr hr1 hband
  refine ⟨hT, h0, hbr, hr1, hlo, hhi.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hrate hC).trans_eq (by ring)

private theorem tendsto_inv_one_add_loglog :
    Tendsto (fun T : ℝ => (1 + Real.log (Real.log T))⁻¹) atTop (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ => 1 + Real.log (Real.log T)) atTop atTop := by
    apply tendsto_atTop.2
    intro a
    have he := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (a - 1)
    filter_upwards [he] with T hT
    change a - 1 ≤ Real.log (Real.log T) at hT
    linarith
  exact (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp ht

theorem positive_extended_shoulder_mass_tendsto_zero (h : BGSTBPositiveCutoffEstimate) :
    Tendsto (fun T : ℝ =>
      ∫ α in centralFourierRadius T..extendedShoulderRadius T, formFactor T α)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hm⟩ := eventually_positive_extended_shoulder_mass_le h
  apply squeeze_zero' (hm.mono fun _ h => h.2.2.2.2.1) (hm.mono fun _ h => h.2.2.2.2.2)
  simpa only [mul_zero, div_eq_mul_inv] using tendsto_inv_one_add_loglog.const_mul C

/-- The complementary Fourier statistic after removing the extended core. -/
def fejerOutsideExtended (T R : ℝ) : ℝ :=
  fejerFormFactor T R - (1 / R) * ∫ α in (-extendedShoulderRadius T)..extendedShoulderRadius T,
    (1 - |α| / R) * formFactor T α

theorem fejerOutsideCentral_sub_outsideExtended_eq (T R : ℝ) :
    fejerOutsideCentral T R - fejerOutsideExtended T R =
      (2 / R) * ∫ α in centralFourierRadius T..extendedShoulderRadius T,
        (1 - |α| / R) * formFactor T α := by
  let g : ℝ → ℝ := fun α => (1 - |α| / R) * formFactor T α
  have hF := MontgomeryGaussianSmoothing.continuous_formFactor T
  have hg : Continuous g := by dsimp [g]; fun_prop
  have he (α : ℝ) : g (-α) = g α := by simp only [g, abs_neg, formFactor_even]
  have hs (b : ℝ) : (∫ u in (-b)..b, g u) = 2 * ∫ u in (0 : ℝ)..b, g u := by
    have hneg : (∫ u in (-b)..(0 : ℝ), g u) = ∫ u in (0 : ℝ)..b, g u := by
      simpa only [he, neg_zero] using
        (intervalIntegral.integral_comp_neg (f := g) (a := (0 : ℝ)) (b := b)).symm
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (-b) 0) (hg.intervalIntegrable 0 b), hneg, two_mul]
  let b := centralFourierRadius T
  let r := extendedShoulderRadius T
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 b) (hg.intervalIntegrable b r)
  change (fejerFormFactor T R - (1 / R) * ∫ α in (-b)..b, g α) -
    (fejerFormFactor T R - (1 / R) * ∫ α in (-r)..r, g α) =
      (2 / R) * ∫ α in b..r, g α
  rw [hs b, hs r, ← hsplit]
  ring

/-- Uniformly in every Fejér radius at least one, the discarded shoulder
has the stated nonnegative contribution and error budget. -/
theorem eventually_fejer_outsideExtended_error (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 1 ≤ R →
      0 ≤ fejerOutsideCentral T R - fejerOutsideExtended T R ∧
      fejerOutsideCentral T R - fejerOutsideExtended T R ≤
        (2 * C / R) * (1 + Real.log (Real.log T))⁻¹ := by
  obtain ⟨C, hC, hm⟩ := eventually_positive_extended_shoulder_mass_le h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hm] with T hm
  obtain ⟨hT, hb0, hbr, hr1, _, hmass⟩ := hm
  intro R hR
  let b := centralFourierRadius T
  let r := extendedShoulderRadius T
  let g : ℝ → ℝ := fun α => (1 - |α| / R) * formFactor T α
  have hR0 := zero_lt_one.trans_le hR
  have hw (α : ℝ) (hα : α ∈ Icc b r) : 0 ≤ 1 - |α| / R ∧ 1 - |α| / R ≤ 1 := by
    have hα0 := hb0.trans hα.1
    rw [abs_of_nonneg hα0]
    exact ⟨sub_nonneg.mpr ((div_le_iff₀ hR0).mpr (by simpa using hα.2.trans (hr1.trans hR))),
      sub_le_self 1 (div_nonneg hα0 hR0.le)⟩
  have hF := MontgomeryGaussianSmoothing.continuous_formFactor T
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hi0 := intervalIntegral.integral_nonneg (μ := volume) hbr
    (fun α hα => mul_nonneg (hw α hα).1 (formFactor_nonneg hT α))
  have hi := intervalIntegral.integral_mono_on (μ := volume) hbr (hg.intervalIntegrable b r)
    (hF.intervalIntegrable b r) (fun α hα =>
      mul_le_of_le_one_left (formFactor_nonneg hT α) (hw α hα).2)
  rw [fejerOutsideCentral_sub_outsideExtended_eq]
  refine ⟨mul_nonneg (by positivity) hi0, ?_⟩
  exact (mul_le_mul_of_nonneg_left (hi.trans hmass) (by positivity : 0 ≤ 2 / R)).trans_eq
    (by rw [div_eq_mul_inv C]; ring)

theorem density_one_of_fejer_outside_extended_upper (h : BGSTBPositiveCutoffEstimate)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ᶠ T : ℝ in atTop,
      fejerOutsideExtended T R ≤ 1 - 1 / R + ε) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  apply density_one_of_fejer_outside_central_upper h
  intro ε hε
  obtain ⟨R, hR, hu⟩ := hupper (ε / 2) (by positivity)
  obtain ⟨C, _, hd⟩ := eventually_fejer_outsideExtended_error h
  have hz := tendsto_inv_one_add_loglog.const_mul (2 * C / R)
  rw [mul_zero] at hz
  refine ⟨R, hR, ?_⟩
  filter_upwards [hu, hd, hz.eventually_le_const (show 0 < ε / 2 by positivity)]
    with T hT hdiff hsmall
  have hle := (hdiff R hR).2.trans hsmall
  linarith only [hT, hle]

end RiemannResearch.Analysis.MontgomeryFormFactor
