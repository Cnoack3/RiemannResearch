/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryTransitionFrequency
import RiemannResearch.Analysis.MontgomeryGaussianSmoothing
import RiemannResearch.Analysis.MontgomeryHorizontalPairing
import RiemannResearch.Analysis.MontgomeryLoglogTransfer
import RiemannResearch.Analysis.MontgomeryFejerDensity
import RiemannResearch.Analysis.ActualZeroCollisionDensity
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.EvenIntegralHalfLine
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local mass of the raw Montgomery form factor

The corrected BGSTB positive-cutoff estimate (arXiv:2501.14545v3, (3.5))
and the checked logarithmic-band comparison give the local L1 law in
Section 2 of the user-provided note `Montgomery_Pair_Correlation_Without_RH.md`.
The BGSTB estimate is an explicit premise. The frequency band shrinks
to zero, and the result concerns its contribution to Fourier test integrals.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate MontgomeryHorizontalBessel MontgomeryHorizontalTransfer
open ActualZeroCollisionCertificate

private theorem eventually_core_bounds :
    ∀ᶠ T : ℝ in atTop,
      let L := Real.log T
      let ℓ := Real.log L
      1 < T ∧ 1 ≤ L ∧ 1 ≤ ℓ ∧ ℓ ≤ L ∧ ℓ ^ 2 / Real.sqrt L ≤ 1 ∧
        ℓ ≤ horizontalTailDecay T / 4 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    (loglog_pow_div_log_tendsto_zero 2).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 32),
    (loglog_pow_div_log_tendsto_zero 4).eventually_le_const zero_lt_one]
    with T hT hL1 hℓ1 hband hsmall
  let L := Real.log T
  let ℓ := Real.log L
  have hL : 0 < L := Real.log_pos hT
  change 1 ≤ ℓ at hℓ1
  change ℓ ^ 2 / L ≤ 1 / 32 at hband
  change ℓ ^ 4 / L ≤ 1 at hsmall
  have hℓ : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
  refine ⟨hT, hL1, hℓ1, (Real.log_le_sub_one_of_pos hL).trans (sub_le_self _ zero_le_one),
    ?_, ?_⟩
  · apply (sq_le_sq₀ (by positivity) zero_le_one).mp
    rw [div_pow, Real.sq_sqrt hL.le, one_pow, show (ℓ ^ 2) ^ 2 = ℓ ^ 4 by ring]
    exact hsmall
  · change ℓ ≤ L / (8 * ℓ) / 4
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4),
      le_div_iff₀ (mul_pos (by norm_num) hℓ)]
    nlinarith only [(div_le_iff₀ hL).mp hband]

private theorem one_add_mul_exp_neg_le (u : ℝ) :
    (1 + u) * Real.exp (-u) ≤ 2 * Real.exp (-u / 2) := by
  have h : 1 + u ≤ 2 * Real.exp (u / 2) := by
    linarith [Real.add_one_le_exp (u / 2)]
  calc
    _ ≤ (2 * Real.exp (u / 2)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add, show u / 2 + -u = -u / 2 by ring]

private theorem abs_sub_le_sqrt_error {f s : ℝ} (hf : 0 ≤ f) (hs : 0 ≤ s) :
    |f - s| ≤
      2 * Real.sqrt s * |Real.sqrt s - Real.sqrt f| + |Real.sqrt s - Real.sqrt f| ^ 2 := by
  let e := Real.sqrt f - Real.sqrt s
  have hid : f - s = 2 * Real.sqrt s * e + e ^ 2 := by
    dsimp only [e]
    nlinarith only [Real.sq_sqrt hf, Real.sq_sqrt hs]
  rw [hid]
  calc
    _ ≤ |2 * Real.sqrt s * e| + |e ^ 2| := abs_add_le _ _
    _ = _ := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt s), abs_pow]
      simp [e, abs_sub_comm]

/-- An integrable exponential majorant plus a bounded error on the positive
half of the central phase interval. -/
theorem eventually_raw_central_peak_error (h : BGSTBPositiveCutoffEstimate) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop,
      ∀ u ∈ Icc (0 : ℝ) (Real.log (Real.log T)),
        |formFactor T (u / Real.log T) - Real.exp (-2 * u) * Real.log T| ≤
          A * Real.log (Real.log T) * Real.exp (-u / 2) + B := by
  obtain ⟨C, hC, hcomplex⟩ := sharpFormFactor_bound_of_bgstb h
  obtain ⟨K, hK, htransfer⟩ := eventually_sqrt_formFactor_difference_loglog_band
  let J := Real.sqrt (2 * C + 1)
  have hJ : 0 ≤ J := Real.sqrt_nonneg _
  refine ⟨4 * K, 4 * K * J + (2 * K) ^ 2 + (2 * C + 1), by positivity, by positivity, ?_⟩
  filter_upwards [hcomplex, htransfer, eventually_core_bounds] with T hc ht hb
  obtain ⟨hT, hL1, hℓ1, hℓL, hsmall, hband⟩ := hb
  intro u hu
  let L := Real.log T
  let ℓ := Real.log L
  let α := u / L
  let s := sharpFormFactor T α
  let f := formFactor T α
  let q := Real.exp (-2 * u)
  let e := |Real.sqrt s - Real.sqrt f|
  let M := Real.sqrt L * Real.exp (-u)
  have hL : 0 < L := Real.log_pos hT
  have hℓ : 0 ≤ ℓ := zero_le_one.trans hℓ1
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hroot1 : 1 ≤ Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL1
  have huα : α * L = u := div_mul_cancel₀ _ hL.ne'
  have hα : α ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hu.1 hL.le, (div_le_iff₀ hL).mpr (by simpa using hu.2.trans hℓL)⟩
  have hq : q ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hu.1])
  have hinv : 1 / Real.sqrt L ≤ 1 := (div_le_iff₀ hroot).mpr (by simpa using hroot1)
  have hs0 : 0 ≤ s := MontgomeryHorizontalPairing.sharpFormFactor_nonneg hT α
  have hf0 : 0 ≤ f := formFactor_nonneg hT α
  have he0 : 0 ≤ e := abs_nonneg _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcomplex' : |s - (q * L + α)| ≤ C * (q + 1 / Real.sqrt L) := by
    simpa only [s, q, L, huα] using hc α hα
  have hs : |s - q * L| ≤ 2 * C + 1 := by
    calc
      _ = |(s - (q * L + α)) + α| := by ring_nf
      _ ≤ |s - (q * L + α)| + |α| := abs_add_le _ _
      _ ≤ C * (q + 1 / Real.sqrt L) + 1 := by
        rw [abs_of_nonneg hα.1]
        exact add_le_add hcomplex' hα.2
      _ ≤ _ := by
        have htwo : q + 1 / Real.sqrt L ≤ 2 := by linarith
        linarith only [mul_le_mul_of_nonneg_left htwo hC]
  have hM2 : M ^ 2 = q * L := by
    dsimp only [M, q]
    rw [mul_pow, Real.sq_sqrt hL.le, pow_two, ← Real.exp_add,
      show -u + -u = -2 * u by ring, mul_comm]
  have hsroot : Real.sqrt s ≤ M + J := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg hM hJ)).mp
    have hJ2 : J ^ 2 = 2 * C + 1 := Real.sq_sqrt (by positivity)
    rw [Real.sq_sqrt hs0, add_sq, hM2, hJ2]
    linarith only [(abs_le.mp hs).2, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM) hJ]
  have he' : e ≤ K * ((1 + u) * (ℓ / Real.sqrt L)) := by
    have hcomp := ht α (by rw [huα, abs_of_nonneg hu.1]; exact hu.2.trans hband)
    change e ≤ K * Real.sqrt ((1 + (α * L) ^ 2) * horizontalLogRate T) at hcomp
    rw [huα] at hcomp
    apply hcomp.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    have hr : 0 ≤ (1 + u) * (ℓ / Real.sqrt L) :=
      mul_nonneg (by linarith only [hu.1]) (div_nonneg hℓ hroot.le)
    calc
      _ ≤ Real.sqrt (((1 + u) * (ℓ / Real.sqrt L)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        change (1 + u ^ 2) * (ℓ ^ 2 / L) ≤ ((1 + u) * (ℓ / Real.sqrt L)) ^ 2
        rw [mul_pow, div_pow, Real.sq_sqrt hL.le]
        exact mul_le_mul_of_nonneg_right (by nlinarith only [hu.1]) (by positivity)
      _ = _ := Real.sqrt_sq hr
  have he2 : e ≤ 2 * K := by
    apply he'.trans
    have hu2 : 1 + u ≤ 2 * ℓ := by linarith only [hu.2, hℓ1]
    have hm := mul_le_mul_of_nonneg_right hu2 (div_nonneg hℓ hroot.le)
    have hid : (2 * ℓ) * (ℓ / Real.sqrt L) = 2 * (ℓ ^ 2 / Real.sqrt L) := by ring
    rw [hid] at hm
    have hle : (1 + u) * (ℓ / Real.sqrt L) ≤ 2 := hm.trans (by linarith only [hsmall])
    exact (mul_le_mul_of_nonneg_left hle hK.le).trans_eq (mul_comm _ _)
  have hMe : M * e ≤ (2 * K) * ℓ * Real.exp (-u / 2) := by
    calc
      _ ≤ M * (K * ((1 + u) * (ℓ / Real.sqrt L))) :=
        mul_le_mul_of_nonneg_left he' hM
      _ = (K * ℓ) * ((1 + u) * Real.exp (-u)) := by
        dsimp only [M]
        field_simp [hroot.ne']
      _ ≤ (K * ℓ) * (2 * Real.exp (-u / 2)) :=
        mul_le_mul_of_nonneg_left (one_add_mul_exp_neg_le u) (mul_nonneg hK.le hℓ)
      _ = _ := by ring
  have hF : |f - s| ≤
      (4 * K) * ℓ * Real.exp (-u / 2) + 4 * K * J + (2 * K) ^ 2 := by
    have hs' := mul_le_mul_of_nonneg_right hsroot he0
    have hJe := mul_le_mul_of_nonneg_left he2 hJ
    have heSq : e ^ 2 ≤ (2 * K) ^ 2 := (sq_le_sq₀ he0 (by positivity)).mpr he2
    have hsqerr := abs_sub_le_sqrt_error hf0 hs0
    change |f - s| ≤ 2 * Real.sqrt s * e + e ^ 2 at hsqerr
    linarith only [hs', hJe, heSq, hsqerr, hMe]
  change |f - q * L| ≤ _
  calc
    _ = |(f - s) + (s - q * L)| := by ring_nf
    _ ≤ |f - s| + |s - q * L| := abs_add_le _ _
    _ ≤ _ := by linarith only [hF, hs]

private theorem integral_exp_neg_mul (a b : ℝ) (ha : a ≠ 0) :
    (∫ u in (0 : ℝ)..b, Real.exp (-a * u)) = (1 - Real.exp (-a * b)) / a := by
  rw [intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.mpr ha), smul_eq_mul, mul_zero]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => Real.hasDerivAt_exp u) (Real.continuous_exp.intervalIntegrable _ _),
    Real.exp_zero, inv_neg]
  ring

private theorem integral_symmetric_of_even {f : ℝ → ℝ} (hf : Continuous f)
    (heven : ∀ u, f (-u) = f u) (b : ℝ) :
    (∫ u in (-b)..b, f u) = 2 * ∫ u in (0 : ℝ)..b, f u := by
  have hs : (∫ u in (-b)..(0 : ℝ), f u) = ∫ u in (0 : ℝ)..b, f u := by
    simpa only [heven, neg_zero] using
      (intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := b)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-b) 0) (hf.intervalIntegrable 0 b), hs, two_mul]

/-- Rescaled L1 approximation on the central interval, with the error
of order log log(T) / log(T). -/
theorem eventually_raw_central_peak_local_L1 (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      let L := Real.log T
      let ℓ := Real.log L
      (∫ u in (-ℓ)..ℓ, |formFactor T (u / L) / L - Real.exp (-2 * |u|)|) ≤
        C * (ℓ / L) := by
  obtain ⟨A, B, hA, hB, hmajor⟩ := eventually_raw_central_peak_error h
  refine ⟨2 * (2 * A + B), by positivity, ?_⟩
  filter_upwards [hmajor, eventually_core_bounds] with T hbound hcore
  obtain ⟨hT, _, hℓ1, _, _, _⟩ := hcore
  let L := Real.log T
  let ℓ := Real.log L
  let f := fun u : ℝ => |formFactor T (u / L) / L - Real.exp (-2 * |u|)|
  let g := fun u : ℝ => (A * ℓ * Real.exp (-u / 2) + B) / L
  have hL : 0 < L := Real.log_pos hT
  have hℓ : 0 ≤ ℓ := zero_le_one.trans hℓ1
  have hf : Continuous f := by
    have := MontgomeryGaussianSmoothing.continuous_formFactor T
    dsimp [f]
    fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have heven (u : ℝ) : f (-u) = f u := by
    simp only [f, neg_div, formFactor_even, abs_neg]
  have hmono : (∫ u in (0 : ℝ)..ℓ, f u) ≤ ∫ u in (0 : ℝ)..ℓ, g u := by
    apply intervalIntegral.integral_mono_on hℓ (hf.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)
    intro u hu
    have heq : f u = |formFactor T (u / L) - Real.exp (-2 * u) * L| / L := by
      dsimp only [f]
      rw [abs_of_nonneg hu.1]
      calc
        _ = |(formFactor T (u / L) - Real.exp (-2 * u) * L) / L| := by
          rw [sub_div, mul_div_cancel_right₀ _ hL.ne']
        _ = _ := by rw [abs_div, abs_of_pos hL]
    rw [heq]
    exact div_le_div_of_nonneg_right (hbound u hu) hL.le
  have hgInt : (∫ u in (0 : ℝ)..ℓ, g u) ≤ (2 * A + B) * (ℓ / L) := by
    dsimp only [g]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun u : ℝ => A * ℓ * Real.exp (-u / 2))).intervalIntegrable
        _ _) intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have heval : (∫ u in (0 : ℝ)..ℓ, Real.exp (-u / 2)) ≤ 2 := by
      simp_rw [show ∀ u : ℝ, -u / 2 = -(1 / 2) * u by intro u; ring]
      rw [integral_exp_neg_mul _ _ (by norm_num)]
      linarith [Real.exp_pos (-(1 / 2) * ℓ)]
    calc
      _ ≤ (A * ℓ * 2 + ℓ * B) / L := by
        apply div_le_div_of_nonneg_right _ hL.le
        exact add_le_add (mul_le_mul_of_nonneg_left heval (mul_nonneg hA hℓ)) le_rfl
      _ = _ := by ring
  change (∫ u in (-ℓ)..ℓ, f u) ≤ _
  rw [integral_symmetric_of_even hf heven ℓ]
  linarith only [hmono, hgInt]

/-- Central rescaled profile, extended by zero outside the phase interval. -/
def rawCentralProfile (T : ℝ) : ℝ → ℝ :=
  (Icc (-Real.log (Real.log T)) (Real.log (Real.log T))).indicator
    (fun u => formFactor T (u / Real.log T) / Real.log T)

private theorem integrable_rawCentralProfile (T : ℝ) : Integrable (rawCentralProfile T) := by
  have hc : Continuous (fun u : ℝ => formFactor T (u / Real.log T) / Real.log T) := by
    have := MontgomeryGaussianSmoothing.continuous_formFactor T
    fun_prop
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

private theorem integrable_exp_neg_two_abs :
    Integrable (fun u : ℝ => Real.exp (-2 * |u|)) := by
  have hl := integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) 0
  have hr := integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0
  have hleft : EqOn (fun u : ℝ => Real.exp (2 * u)) (fun u => Real.exp (-2 * |u|)) (Iic 0) := by
    intro u hu
    change u ≤ 0 at hu
    change Real.exp (2 * u) = Real.exp (-2 * |u|)
    rw [abs_of_nonpos hu]
    congr 1
    ring
  have hright : EqOn (fun u : ℝ => Real.exp (-2 * u)) (fun u => Real.exp (-2 * |u|)) (Ioi 0) := by
    intro u hu
    change 0 < u at hu
    change Real.exp (-2 * u) = Real.exp (-2 * |u|)
    rw [abs_of_pos hu]
  simpa only [Iic_union_Ioi, integrableOn_univ] using
    (hl.congr_fun hleft measurableSet_Iic).union (hr.congr_fun hright measurableSet_Ioi)

private theorem integral_exp_neg_two_abs :
    (∫ u : ℝ, Real.exp (-2 * |u|)) = 1 := by
  rw [integral_eq_two_smul_Ioi_of_even _ integrable_exp_neg_two_abs (by simp)]
  have heq : (∫ u in Ioi (0 : ℝ), Real.exp (-2 * |u|)) =
      ∫ u in Ioi (0 : ℝ), Real.exp (-2 * u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change 0 < u at hu
    change Real.exp (-2 * |u|) = Real.exp (-2 * u)
    rw [abs_of_pos hu]
  rw [heq, integral_exp_mul_Ioi (a := -2) (by norm_num) 0]
  norm_num [smul_eq_mul]

private theorem integral_exp_neg_two_abs_interval {b : ℝ} (hb : 0 ≤ b) :
    (∫ u in (-b)..b, Real.exp (-2 * |u|)) = 1 - Real.exp (-2 * b) := by
  rw [integral_symmetric_of_even (by fun_prop) (by simp)]
  have heq : (∫ u in (0 : ℝ)..b, Real.exp (-2 * |u|)) =
      ∫ u in (0 : ℝ)..b, Real.exp (-2 * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hb] at hu
    change Real.exp (-2 * |u|) = Real.exp (-2 * u)
    rw [abs_of_nonneg hu.1]
  rw [heq, integral_exp_neg_mul 2 b (by norm_num)]
  ring

/-- The global L1 error is the central interval error plus the exact exponential tail. -/
theorem raw_central_peak_L1_eq {T : ℝ} (hℓ : 0 ≤ Real.log (Real.log T)) :
    let L := Real.log T
    let ℓ := Real.log L
    (∫ u : ℝ, |rawCentralProfile T u - Real.exp (-2 * |u|)|) =
      (∫ u in (-ℓ)..ℓ, |formFactor T (u / L) / L - Real.exp (-2 * |u|)|) +
        Real.exp (-2 * ℓ) := by
  let L := Real.log T
  let ℓ := Real.log L
  let s := Icc (-ℓ) ℓ
  let p := fun u : ℝ => Real.exp (-2 * |u|)
  let f := fun u : ℝ => |rawCentralProfile T u - p u|
  have hs : MeasurableSet s := measurableSet_Icc
  have horder : -ℓ ≤ ℓ := by linarith
  have hf : Integrable f := ((integrable_rawCentralProfile T).sub
    integrable_exp_neg_two_abs).abs
  have htail : (∫ u in sᶜ, f u) = ∫ u in sᶜ, p u := by
    apply setIntegral_congr_fun hs.compl
    intro u hu
    change u ∉ s at hu
    change |s.indicator (fun x => formFactor T (x / L) / L) u - p u| = p u
    rw [indicator_of_notMem hu, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)]
  have hp := integral_add_compl hs integrable_exp_neg_two_abs
  rw [integral_exp_neg_two_abs] at hp
  change (∫ u in s, p u) + (∫ u in sᶜ, p u) = 1 at hp
  have hp' : (∫ u in s, p u) = 1 - Real.exp (-2 * ℓ) := by
    change (∫ u in Icc (-ℓ) ℓ, Real.exp (-2 * |u|)) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le horder]
    exact integral_exp_neg_two_abs_interval hℓ
  have hcenter : (∫ u in s, f u) =
      ∫ u in (-ℓ)..ℓ, |formFactor T (u / L) / L - p u| := by
    rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun hs
    intro u hu
    change |s.indicator (fun x => formFactor T (x / L) / L) u - p u| =
      |formFactor T (u / L) / L - p u|
    rw [indicator_of_mem hu]
  change (∫ u, f u) = _
  rw [← integral_add_compl hs hf, hcenter, htail]
  linarith only [hp, hp']

/-- The rescaled central profile has the full-line L1 rate in the note.
The paper's positive-cutoff estimate is the analytic premise. -/
theorem eventually_raw_central_peak_L1 (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      (∫ u : ℝ, |rawCentralProfile T u - Real.exp (-2 * |u|)|) ≤
        C * (Real.log (Real.log T) / Real.log T) := by
  obtain ⟨C, hC, hlocal⟩ := eventually_raw_central_peak_local_L1 h
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [hlocal, eventually_core_bounds] with T hbound hcore
  obtain ⟨hT, _, hℓ1, _, _, _⟩ := hcore
  let L := Real.log T
  let ℓ := Real.log L
  have hL : 0 < L := Real.log_pos hT
  have hℓ : 0 ≤ ℓ := zero_le_one.trans hℓ1
  have htail : Real.exp (-2 * ℓ) ≤ ℓ / L := by
    calc
      _ ≤ Real.exp (-ℓ) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / L := by rw [Real.exp_neg, Real.exp_log hL, one_div]
      _ ≤ _ := div_le_div_of_nonneg_right hℓ1 hL.le
  rw [raw_central_peak_L1_eq hℓ]
  change _ ≤ (C + 1) * (ℓ / L)
  linarith only [hbound, htail]

/-- The radius of the core in the original Fourier-frequency variable. -/
def centralFourierRadius (T : ℝ) : ℝ := Real.log (Real.log T) / Real.log T

theorem centralFourierRadius_tendsto_zero :
    Tendsto centralFourierRadius atTop (𝓝 0) := by
  change Tendsto (fun T : ℝ => Real.log (Real.log T) / Real.log T) atTop (𝓝 0)
  simpa only [pow_one] using loglog_pow_div_log_tendsto_zero 1

private theorem integral_rawCentralProfile {T : ℝ} (hT : 1 < T)
    (hℓ : 0 ≤ Real.log (Real.log T)) :
    (∫ u, rawCentralProfile T u) =
      ∫ α in (-centralFourierRadius T)..centralFourierRadius T, formFactor T α := by
  let L := Real.log T
  let ℓ := Real.log L
  have hL := Real.log_pos hT
  have ho : -ℓ ≤ ℓ := by linarith
  rw [rawCentralProfile, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ho, intervalIntegral.integral_div]
  have harg (u : ℝ) : u / L = L⁻¹ * u := by rw [div_eq_mul_inv, mul_comm]
  change (∫ u in (-ℓ)..ℓ, formFactor T (u / L)) / L = _
  simp_rw [harg]
  rw [intervalIntegral.integral_comp_mul_left _ (inv_ne_zero hL.ne'),
    inv_inv, smul_eq_mul, mul_neg, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  have hb : L⁻¹ * ℓ = centralFourierRadius T := (harg ℓ).symm
  rw [hb]

/-- The central frequency interval supplies one unit of Fourier mass with
the same log-log over log error as the profile. -/
theorem eventually_raw_central_mass_error (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      |(∫ α in (-centralFourierRadius T)..centralFourierRadius T, formFactor T α) - 1| ≤
        C * centralFourierRadius T := by
  obtain ⟨C, hC, hfull⟩ := eventually_raw_central_peak_L1 h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfull, eventually_core_bounds] with T hbound hcore
  obtain ⟨hT, _, hℓ1, _, _, _⟩ := hcore
  have hInt := integral_rawCentralProfile hT (zero_le_one.trans hℓ1)
  rw [← hInt, ← integral_exp_neg_two_abs, ← integral_sub (integrable_rawCentralProfile T)
    integrable_exp_neg_two_abs]
  have hI := norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
    (fun u : ℝ => rawCentralProfile T u - Real.exp (-2 * |u|))
  simp only [Real.norm_eq_abs] at hI
  exact hI.trans hbound

theorem raw_central_mass_tendsto_one (h : BGSTBPositiveCutoffEstimate) :
    Tendsto (fun T : ℝ =>
      ∫ α in (-centralFourierRadius T)..centralFourierRadius T, formFactor T α) atTop (𝓝 1) := by
  obtain ⟨C, _, hmass⟩ := eventually_raw_central_mass_error h
  have hz : Tendsto (fun T : ℝ => C * centralFourierRadius T) atTop (𝓝 0) := by
    simpa only [mul_zero] using centralFourierRadius_tendsto_zero.const_mul C
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun T => dist_nonneg) ?_ hz
  filter_upwards [hmass] with T hT
  simpa only [Real.dist_eq] using hT

/-- Every continuous Fourier test receives its value at zero from the central
frequency interval. -/
theorem raw_central_test_tendsto_value (h : BGSTBPositiveCutoffEstimate)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun T : ℝ =>
      ∫ α in (-centralFourierRadius T)..centralFourierRadius T, f α * formFactor T α)
      atTop (𝓝 (f 0)) := by
  let b := centralFourierRadius
  let M := fun T : ℝ => ∫ α in (-(b T))..(b T), formFactor T α
  let I := fun T : ℝ => ∫ α in (-(b T))..(b T), f α * formFactor T α
  have hM : Tendsto M atTop (𝓝 1) := raw_central_mass_tendsto_one h
  have hErr : Tendsto (fun T => I T - f 0 * M T) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hf0 : ContinuousAt f (0 : ℝ) := hf.continuousAt
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hf0 (ε / 3) (by positivity)
    filter_upwards [centralFourierRadius_tendsto_zero.eventually (gt_mem_nhds hδ),
      hM.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)), eventually_core_bounds]
      with T hb hm hcore
    obtain ⟨hT, _, hℓ1, _, _, _⟩ := hcore
    have hbt : 0 ≤ b T := div_nonneg (zero_le_one.trans hℓ1) (Real.log_pos hT).le
    have horder : -(b T) ≤ b T := by linarith
    have hF := MontgomeryGaussianSmoothing.continuous_formFactor T
    have hcont : Continuous (fun α => (f α - f 0) * formFactor T α) :=
      (hf.sub continuous_const).mul hF
    have heq : I T - f 0 * M T =
        ∫ α in (-(b T))..(b T), (f α - f 0) * formFactor T α := by
      have hleft : Continuous (fun α => f α * formFactor T α) := hf.mul hF
      have hright : Continuous (fun α => f 0 * formFactor T α) := hF.const_mul (f 0)
      simp only [I, M, sub_mul]
      rw [intervalIntegral.integral_sub (hleft.intervalIntegrable _ _)
        (hright.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    have hmono : (∫ α in (-(b T))..(b T), |(f α - f 0) * formFactor T α|) ≤
        (ε / 3) * M T := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on horder (hcont.abs.intervalIntegrable _ _)
        ((hF.const_mul (ε / 3)).intervalIntegrable _ _)
      intro α hα
      have hdα : dist α 0 < δ := by
        rw [Real.dist_eq, sub_zero]
        exact (abs_le.mpr hα).trans_lt hb
      have heα : |f α - f 0| ≤ ε / 3 := by
        simpa only [Real.dist_eq] using (hd hdα).le
      have hpos := formFactor_nonneg hT α
      rw [abs_mul, abs_of_nonneg hpos]
      exact mul_le_mul_of_nonneg_right heα hpos
    rw [Real.dist_eq, sub_zero, heq]
    have hn := intervalIntegral.norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
      (f := fun α => (f α - f 0) * formFactor T α) horder
    simp only [Real.norm_eq_abs] at hn
    refine (hn.trans hmono).trans_lt ?_
    calc
      _ < (ε / 3) * 2 := mul_lt_mul_of_pos_left hm (by positivity)
      _ < _ := by linarith
  have h := hErr.add (hM.const_mul (f 0))
  simpa only [sub_add_cancel, mul_one, zero_add] using h

/-- The part of the triangular Fourier test inside the shrinking core. -/
def fejerCentralContribution (T R : ℝ) : ℝ :=
  (1 / R) * ∫ α in (-centralFourierRadius T)..centralFourierRadius T,
    (1 - |α| / R) * formFactor T α

/-- The signed remainder after removing the central part of the Fejér test. -/
def fejerOutsideCentral (T R : ℝ) : ℝ :=
  fejerFormFactor T R - fejerCentralContribution T R

theorem fejer_central_tendsto (h : BGSTBPositiveCutoffEstimate) (R : ℝ) :
    Tendsto (fun T : ℝ => fejerCentralContribution T R) atTop (𝓝 (1 / R)) := by
  have hc : Continuous (fun α : ℝ => 1 - |α| / R) := by fun_prop
  simpa [fejerCentralContribution] using (raw_central_test_tendsto_value h hc).const_mul (1 / R)

theorem fejer_outside_central_model_tendsto
    (h : BGSTBPositiveCutoffEstimate) (hpcc : RawFormFactorTestLimit) {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (fun T : ℝ => fejerOutsideCentral T R) atTop (𝓝 (1 - 1 / R + 1 / (3 * R ^ 2))) := by
  have ht := (fejer_limit_of_rawFormFactorTestLimit hpcc hR).sub (fejer_central_tendsto h R)
  have he : 1 + 1 / (3 * R ^ 2) - 1 / R = 1 - 1 / R + 1 / (3 * R ^ 2) := by ring
  simpa only [fejerOutsideCentral, he] using ht

/-- With the core evaluated, upper bounds on the complementary part at
suitable fixed radii suffice for the joint simple and critical density. -/
theorem density_one_of_fejer_outside_central_upper (h : BGSTBPositiveCutoffEstimate)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ᶠ T : ℝ in atTop,
      fejerOutsideCentral T R ≤ 1 - 1 / R + ε) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  apply density_one_of_collision_limit
  apply collision_limit_of_fejer_upper
  intro ε hε
  obtain ⟨R, hR, htail⟩ := hupper (ε / 3) (by positivity)
  refine ⟨R, zero_lt_one.trans_le hR, ?_⟩
  have hcore := (fejer_central_tendsto h R).eventually
    (gt_mem_nhds (show 1 / R < 1 / R + ε / 3 by linarith))
  filter_upwards [htail, hcore] with T htail' hcore'
  unfold fejerOutsideCentral at htail'
  linarith only [htail', hcore', hε]

end RiemannResearch.Analysis.MontgomeryFormFactor
