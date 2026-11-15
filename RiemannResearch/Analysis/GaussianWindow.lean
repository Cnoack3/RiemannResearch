/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Exact Gaussian window accounting and quantitative desmoothing

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Section 3.3, equations (3.3.1)--(3.3.5), pp. 115--116:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supports the Gaussian smoothing strategy and scale convention.

The exact missing window mass and complete source tails are retained first.
The universal loss is then bounded by `sqrt 2 * exp (-a * H^2 / 2)`.
Absorbing that relative loss avoids a separate unsmoothed moment estimate.
Continuous quadratically bounded functions have genuine whole-line Gaussian
integrals. The final desmoothing theorem is conditional on its displayed
smoothed estimate; it does not prove any zeta moment or arithmetic estimate.

The Conrey--Baluyot application is in `ConreyBaluyotGaussianMoment`.
-/

noncomputable section
open MeasureTheory Set
namespace Real

/-- Normalized Gaussian with precision `a`. Its scale is `a^(-1/2)`. -/
def gaussianDensity (a x : ℝ) : ℝ := Real.exp (-a * x ^ 2) / Real.sqrt (Real.pi / a)

def gaussianWindow (a A B t : ℝ) : ℝ :=
  ∫ u in A..B, gaussianDensity a (t - u)

theorem gaussianDensity_nonneg (a x : ℝ) : 0 ≤ gaussianDensity a x := by
  unfold gaussianDensity
  positivity

theorem continuous_gaussianDensity (a : ℝ) : Continuous (gaussianDensity a) := by
  unfold gaussianDensity
  fun_prop

theorem integrable_gaussianDensity {a : ℝ} (ha : 0 < a) :
    Integrable (gaussianDensity a) :=
  (integrable_exp_neg_mul_sq ha).div_const _

theorem integral_gaussianDensity {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, gaussianDensity a x = 1 := by
  simp only [gaussianDensity, div_eq_mul_inv, integral_mul_const, integral_gaussian]
  exact mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (div_pos Real.pi_pos ha)))

theorem continuous_gaussianWindow (a A B : ℝ) : Continuous (gaussianWindow a A B) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (show Continuous (fun p : ℝ × ℝ => gaussianDensity a (p.1 - p.2)) from
      (continuous_gaussianDensity a).comp (continuous_fst.sub continuous_snd)) A B

/-- Exact missing Gaussian mass, including both tails. -/
theorem gaussianWindow_add_complement {a A B : ℝ} (ha : 0 < a) (hAB : A ≤ B)
    (t : ℝ) :
    gaussianWindow a A B t +
      (∫ u in (Ioc A B)ᶜ, gaussianDensity a (t - u)) = 1 := by
  rw [gaussianWindow, intervalIntegral.integral_of_le hAB,
    integral_add_compl measurableSet_Ioc ((integrable_gaussianDensity ha).comp_sub_left t),
    integral_sub_left_eq_self, integral_gaussianDensity ha]

theorem gaussianWindow_mem_Icc {a A B : ℝ} (ha : 0 < a) (hAB : A ≤ B) (t : ℝ) :
    gaussianWindow a A B t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact intervalIntegral.integral_nonneg hAB (fun u _ => gaussianDensity_nonneg a (t - u))
  · have h := gaussianWindow_add_complement ha hAB t
    have hn : 0 ≤ ∫ u in (Ioc A B)ᶜ, gaussianDensity a (t - u) :=
      integral_nonneg (fun u => gaussianDensity_nonneg a (t - u))
    linarith

theorem sqrt_gaussian_ratio {a : ℝ} (ha : 0 < a) :
    Real.sqrt (Real.pi / (a / 2)) / Real.sqrt (Real.pi / a) = Real.sqrt 2 := by
  have he : Real.pi / (a / 2) = 2 * (Real.pi / a) := by ring
  rw [he, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_div_cancel_right₀]
  exact ne_of_gt (Real.sqrt_pos.2 (div_pos Real.pi_pos ha))

/-- An explicit two-tail bound, uniform in the center and window endpoints. -/
theorem one_sub_gaussianWindow_le {a A B H t : ℝ} (ha : 0 < a) (hH : 0 ≤ H)
    (hAt : A + H ≤ t) (htB : t ≤ B - H) :
    1 - gaussianWindow a A B t ≤ Real.sqrt 2 * Real.exp (-a * H ^ 2 / 2) := by
  have hAB : A ≤ B := by linarith
  let G : ℝ → ℝ := fun u =>
    Real.exp (-a * H ^ 2 / 2) * Real.exp (-(a / 2) * (t - u) ^ 2) / Real.sqrt (Real.pi / a)
  have hG : Integrable G :=
    (((integrable_exp_neg_mul_sq (by linarith : 0 < a / 2)).comp_sub_left t).const_mul
      _).div_const _
  have hpoint : ∀ u ∈ (Ioc A B)ᶜ, gaussianDensity a (t - u) ≤ G u := by
    intro u hu
    have hs : H ^ 2 ≤ (t - u) ^ 2 := by
      have hu' : u ≤ A ∨ B < u := by simpa only [mem_compl_iff, mem_Ioc, not_and_or,
        not_lt, not_le] using hu
      rcases hu' with hu' | hu'
      · have hh : H ≤ t - u := by linarith
        nlinarith
      · have hh : H ≤ u - t := by linarith
        nlinarith
    unfold gaussianDensity
    dsimp [G]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hs)]
  have hbound : (∫ u in (Ioc A B)ᶜ, gaussianDensity a (t - u)) ≤
      ∫ u in (Ioc A B)ᶜ, G u := by
    apply integral_mono_ae ((integrable_gaussianDensity ha).comp_sub_left t).integrableOn
      hG.integrableOn
    exact (ae_restrict_iff' measurableSet_Ioc.compl).mpr (Filter.Eventually.of_forall hpoint)
  have hfull : (∫ u in (Ioc A B)ᶜ, G u) ≤ ∫ u, G u := by
    have he := integral_add_compl (s := Ioc A B) measurableSet_Ioc hG
    have hn : 0 ≤ ∫ u in Ioc A B, G u := integral_nonneg (fun u => by dsimp [G]; positivity)
    linarith
  have hvalue : (∫ u : ℝ, G u) = Real.sqrt 2 * Real.exp (-a * H ^ 2 / 2) := by
    have hshift : (∫ u : ℝ, Real.exp (-(a / 2) * (t - u) ^ 2)) = Real.sqrt (Real.pi / (a / 2)) := by
      rw [integral_sub_left_eq_self (fun x : ℝ => Real.exp (-(a / 2) * x ^ 2)) volume t,
        integral_gaussian]
    calc
      _ = Real.exp (-a * H ^ 2 / 2) * (∫ u : ℝ, Real.exp (-(a / 2) * (t - u) ^ 2)) /
          Real.sqrt (Real.pi / a) := by
        simp only [G, div_eq_mul_inv, integral_mul_const, integral_const_mul]
      _ = Real.exp (-a * H ^ 2 / 2) *
          (Real.sqrt (Real.pi / (a / 2)) / Real.sqrt (Real.pi / a)) := by rw [hshift]; ring
      _ = _ := by rw [sqrt_gaussian_ratio ha]; ring
  have he := gaussianWindow_add_complement ha hAB t
  linarith [hbound.trans (hfull.trans_eq hvalue)]

/-- Gaussian moment with the source variable restricted to a finite interval. -/
def truncatedGaussianMoment (a : ℝ) (f : ℝ → ℝ) (u v x : ℝ) : ℝ :=
  ∫ t in u..v, gaussianDensity a (t - x) * f t

/-- Exact finite Fubini identity; no missing source tails are discarded here. -/
theorem integral_mul_gaussianWindow (a A B u v : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (uIcc u v)) :
    (∫ t in u..v, f t * gaussianWindow a A B t) =
      ∫ x in A..B, truncatedGaussianMoment a f u v x := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => gaussianDensity a (p.1 - p.2) * f p.1)
      (uIcc u v ×ˢ uIcc A B) :=
    ((continuous_gaussianDensity a).comp (continuous_fst.sub continuous_snd)).continuousOn.mul
      (hf.comp continuous_fst.continuousOn (fun p hp => hp.1))
  have hi : IntegrableOn (fun p : ℝ × ℝ => gaussianDensity a (p.1 - p.2) * f p.1)
      (uIoc u v ×ˢ uIoc A B) volume :=
    (hc.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  calc
    _ = ∫ t in u..v, ∫ x in A..B, gaussianDensity a (t - x) * f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change f t * (∫ x in A..B, gaussianDensity a (t - x)) =
        ∫ x in A..B, gaussianDensity a (t - x) * f t
      rw [intervalIntegral.integral_mul_const]
      ring
    _ = _ := intervalIntegral_intervalIntegral_swap hi

/-- The exact unsmoothed moment equals its smoothed part plus the missing mass. -/
theorem gaussianWindow_moment_identity (a A B u v : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (uIcc u v)) :
    (∫ t in u..v, f t) = (∫ x in A..B, truncatedGaussianMoment a f u v x) +
      ∫ t in u..v, (1 - gaussianWindow a A B t) * f t := by
  rw [← integral_mul_gaussianWindow a A B u v f hf,
    ← intervalIntegral.integral_add
      (f := fun t => f t * gaussianWindow a A B t)
      (g := fun t => (1 - gaussianWindow a A B t) * f t)
      (hf.mul (continuous_gaussianWindow a A B).continuousOn).intervalIntegrable
      ((continuousOn_const.sub (continuous_gaussianWindow a A B).continuousOn).mul
        hf).intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro t ht
  ring

/-- Relative smoothing error with an explicit Gaussian tail factor. -/
theorem gaussianWindow_remainder_bounds {a A B H u v : ℝ}
    (ha : 0 < a) (hH : 0 ≤ H) (huv : u ≤ v) (hAu : A + H ≤ u) (hvB : v ≤ B - H)
    {f : ℝ → ℝ} (hf : ContinuousOn f (uIcc u v))
    (hf0 : ∀ t ∈ Icc u v, 0 ≤ f t) :
    0 ≤ (∫ t in u..v, (1 - gaussianWindow a A B t) * f t) ∧
      (∫ t in u..v, (1 - gaussianWindow a A B t) * f t) ≤
        (Real.sqrt 2 * Real.exp (-a * H ^ 2 / 2)) * ∫ t in u..v, f t := by
  have hAB : A ≤ B := by linarith
  constructor
  · apply intervalIntegral.integral_nonneg huv
    intro t ht
    exact mul_nonneg (sub_nonneg.mpr (gaussianWindow_mem_Icc ha hAB t).2) (hf0 t ht)
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on huv
      ((continuousOn_const.sub (continuous_gaussianWindow a A B).continuousOn).mul
        hf).intervalIntegrable
      (continuousOn_const.mul hf).intervalIntegrable
    intro t ht
    exact mul_le_mul_of_nonneg_right (one_sub_gaussianWindow_le ha hH
      (hAu.trans ht.1) (ht.2.trans hvB)) (hf0 t ht)

/-- A finite, quantitative desmoothing theorem. The smoothed estimate is the only
substantive premise; the Gaussian loss is explicit and can be absorbed. -/
theorem integral_le_of_truncatedGaussianMoment {a H u v R : ℝ}
    (ha : 0 < a) (hH : 0 ≤ H) (huv : u ≤ v)
    {f : ℝ → ℝ} (hf : ContinuousOn f (uIcc u v))
    (hf0 : ∀ t ∈ Icc u v, 0 ≤ f t)
    (hsmall : Real.sqrt 2 * Real.exp (-a * H ^ 2 / 2) < 1)
    (hm : (∫ x in (u - H)..(v + H), truncatedGaussianMoment a f u v x) ≤ R) :
    (∫ t in u..v, f t) ≤ R / (1 - Real.sqrt 2 * Real.exp (-a * H ^ 2 / 2)) := by
  have he := gaussianWindow_moment_identity a (u - H) (v + H) u v f hf
  have hb := (gaussianWindow_remainder_bounds (A := u - H) (B := v + H)
    ha hH huv (by linarith) (by linarith) hf hf0).2
  apply (le_div_iff₀ (by linarith : 0 < 1 - Real.sqrt 2 * Real.exp (-a * H ^ 2 / 2))).mpr
  nlinarith

/-- Gaussian damping is integrable against any continuous quadratically bounded function. -/
theorem integrable_gaussianDensity_mul {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ t, ‖f t‖ ≤ C * (1 + t ^ 2)) (u : ℝ) :
    Integrable (fun t => gaussianDensity a (t - u) * f t) := by
  have h0 := (integrable_exp_neg_mul_sq ha).comp_sub_right u
  have h2 : Integrable (fun t : ℝ => (t - u) ^ 2 * Real.exp (-a * (t - u) ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq ha (by norm_num : (-1:ℝ) < (2:ℕ))).comp_sub_right u
  let G : ℝ → ℝ := fun t => C * ((1 + 2 * u ^ 2) * Real.exp (-a * (t - u) ^ 2) +
    2 * ((t - u) ^ 2 * Real.exp (-a * (t - u) ^ 2))) / Real.sqrt (Real.pi / a)
  have hG : Integrable G := (((h0.const_mul _).add (h2.const_mul _)).const_mul C).div_const _
  apply hG.mono' (((continuous_gaussianDensity a).comp
    (continuous_id.sub continuous_const)).mul hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  change ‖gaussianDensity a (t - u) * f t‖ ≤ G t
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (gaussianDensity_nonneg a (t - u))]
  calc
    _ ≤ gaussianDensity a (t - u) * (C * (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left (hb t) (gaussianDensity_nonneg a (t - u))
    _ ≤ G t := by
      dsimp [gaussianDensity, G]
      have hs : 1 + t ^ 2 ≤ 1 + 2 * u ^ 2 + 2 * (t - u) ^ 2 := by nlinarith [sq_nonneg (t - 2 * u)]
      have hh := mul_le_mul_of_nonneg_left hs
        (mul_nonneg hC (Real.exp_nonneg (-a * (t - u) ^ 2)))
      calc
        _ = (C * Real.exp (-a * (t - u) ^ 2) * (1 + t ^ 2)) / Real.sqrt (Real.pi / a) := by ring
        _ ≤ (C * Real.exp (-a * (t - u) ^ 2) * (1 + 2 * u ^ 2 + 2 * (t - u) ^ 2)) /
            Real.sqrt (Real.pi / a) := div_le_div_of_nonneg_right hh (Real.sqrt_nonneg _)
        _ = _ := by ring

/-- Whole-line Gaussian moment, with precision `a`. -/
def gaussianMoment (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, gaussianDensity a (t - x) * f t

/-- Exact source-tail identity for the whole-line moment. -/
theorem gaussianMoment_eq_truncated_add {a u v x : ℝ} (huv : u ≤ v) {f : ℝ → ℝ}
    (hi : Integrable (fun t => gaussianDensity a (t - x) * f t)) :
    gaussianMoment a f x = truncatedGaussianMoment a f u v x +
      ∫ t in (Ioc u v)ᶜ, gaussianDensity a (t - x) * f t := by
  rw [gaussianMoment, truncatedGaussianMoment, intervalIntegral.integral_of_le huv]
  exact (integral_add_compl measurableSet_Ioc hi).symm

theorem truncatedGaussianMoment_le {a u v x : ℝ} (huv : u ≤ v) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) (hi : Integrable (fun t => gaussianDensity a (t - x) * f t)) :
    truncatedGaussianMoment a f u v x ≤ gaussianMoment a f x := by
  rw [gaussianMoment_eq_truncated_add huv hi]
  have hn : 0 ≤ ∫ t in (Ioc u v)ᶜ, gaussianDensity a (t - x) * f t :=
    integral_nonneg (fun t => mul_nonneg (gaussianDensity_nonneg a (t - x)) (hf0 t))
  linarith

/-- A whole-line smoothed bound supplies the finite central moment with explicit loss. -/
theorem integral_le_of_gaussianMoment {a H u v C r : ℝ}
    (ha : 0 < a) (hH : 0 ≤ H) (huv : u ≤ v) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    (hb : ∀ t, ‖f t‖ ≤ C * (1 + t ^ 2))
    (hsmall : Real.sqrt 2 * Real.exp (-a * H ^ 2 / 2) < 1)
    (hm : ∀ x ∈ Icc (u - H) (v + H), gaussianMoment a f x ≤ 1 + r) :
    (∫ t in u..v, f t) ≤ ((v - u + 2 * H) * (1 + r)) /
      (1 - Real.sqrt 2 * Real.exp (-a * H ^ 2 / 2)) := by
  apply integral_le_of_truncatedGaussianMoment ha hH huv hf.continuousOn (fun t _ => hf0 t) hsmall
  have hc : Continuous (truncatedGaussianMoment a f u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (show Continuous (fun p : ℝ × ℝ => gaussianDensity a (p.2 - p.1) * f p.2) from
        ((continuous_gaussianDensity a).comp (continuous_snd.sub continuous_fst)).mul
          (hf.comp continuous_snd)) u v
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : u - H ≤ v + H)
    (hc.intervalIntegrable _ _) (intervalIntegrable_const (c := 1 + r)) (fun x hx =>
      (truncatedGaussianMoment_le huv hf0
        (integrable_gaussianDensity_mul ha hC hf hb x)).trans (hm x hx))
  simpa only [intervalIntegral.integral_const, smul_eq_mul,
    show v + H - (u - H) = v - u + 2 * H by ring] using hi

/-- The precision convention agrees exactly with the usual positive scale convention. -/
theorem gaussianDensity_inv_sq {Δ : ℝ} (hΔ : 0 < Δ) (x : ℝ) :
    gaussianDensity (1 / Δ ^ 2) x = Real.exp (-(x / Δ) ^ 2) / (Δ * Real.sqrt Real.pi) := by
  have hs : Real.sqrt (Real.pi / (1 / Δ ^ 2)) = Δ * Real.sqrt Real.pi := by
    rw [show Real.pi / (1 / Δ ^ 2) = Real.pi * Δ ^ 2 by field_simp,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq_eq_abs,
      abs_of_pos hΔ, mul_comm]
  unfold gaussianDensity
  rw [hs]
  congr 2
  field_simp

/-- The logarithmic padding error is independent of the smoothing scale. -/
theorem gaussian_padding_log_identity {Δ : ℝ} (hΔ : 0 < Δ) (T : ℝ) :
    -(1 / Δ ^ 2) * (Δ * Real.log T) ^ 2 / 2 = -(Real.log T) ^ 2 / 2 := by
  field_simp

/-- An explicit threshold makes the Gaussian desmoothing denominator positive. -/
theorem gaussian_loss_lt_one {a H : ℝ} (hlarge : 2 ≤ a * H ^ 2) :
    Real.sqrt 2 * Real.exp (-a * H ^ 2 / 2) < 1 := by
  have hexp : Real.exp (-a * H ^ 2 / 2) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (a * H ^ 2 / 2)
    have hp := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-a * H ^ 2 / 2))
    have he : Real.exp (a * H ^ 2 / 2) * Real.exp (-a * H ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    rw [he] at hp
    nlinarith [Real.exp_nonneg (-a * H ^ 2 / 2)]
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ Real.sqrt 2 * (1 / 2) := mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)
    _ < 1 := by linarith

/-- The Gaussian logarithmic tail beats any prescribed power at an explicit threshold. -/
theorem exp_neg_log_sq_le_rpow {T k : ℝ} (hT : 0 < T) (hk : 0 ≤ k)
    (hlog : 2 * k ≤ Real.log T) :
    Real.exp (-(Real.log T) ^ 2 / 2) ≤ T ^ (-k) := by
  rw [Real.rpow_def_of_pos hT]
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log T := by linarith
  nlinarith [mul_nonneg hl (sub_nonneg.mpr hlog)]

end Real
