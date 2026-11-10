/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.MontgomeryFormFactor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Gaussian Fourier damping for actual zero pairs

Source: the smoothing-removal obligation in the user-provided Montgomery
continuation. The proof uses the unconditional actual-zero local Cauchy bound
and the elementary inequality `1 - exp (-x ^ 2) ≤ x ^ 2`.
This compares Fourier pairings with Gaussian damping. No identification with
physical-space convolution, pair-correlation asymptotic, RH, or zero-density
assumption is asserted or needed.
-/

noncomputable section
open MeasureTheory
namespace RiemannResearch.Analysis.MontgomeryGaussianSmoothing
open MontgomeryFormFactor

theorem continuous_formFactor (T : ℝ) : Continuous (formFactor T) := by
  unfold formFactor pairSum ZeroOrdinate.phase
  fun_prop

theorem gaussian_damping_error (x : ℝ) :
    0 ≤ 1 - Real.exp (-(x ^ 2)) ∧ 1 - Real.exp (-(x ^ 2)) ≤ x ^ 2 := by
  constructor
  · have h : Real.exp (-(x ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))
    linarith
  · have h := Real.add_one_le_exp (-(x ^ 2))
    linarith

/-- Integrability against a continuous bounded multiplier. -/
theorem integrable_mul_of_abs_le {f F : ℝ → ℝ} (hf : Integrable f)
    (hF : Continuous F) {M : ℝ} (hbound : ∀ x, |F x| ≤ M) :
    Integrable (fun x => f x * F x) := by
  apply (hf.norm.mul_const M).mono'
    (hf.aestronglyMeasurable.mul hF.aestronglyMeasurable)
  filter_upwards with x
  change ‖f x * F x‖ ≤ ‖f x‖ * M
  rw [norm_mul]
  simpa only [Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg (f x))

/-- The signed remainder is retained exactly before estimating its magnitude. -/
theorem gaussian_pairing_difference_eq (f F : ℝ → ℝ) (h : ℝ)
    (hraw : Integrable (fun x => f x * F x))
    (hdamp : Integrable (fun x => f x * Real.exp (-((h * x) ^ 2)) * F x)) :
    (∫ x : ℝ, f x * F x) -
      (∫ x : ℝ, f x * Real.exp (-((h * x) ^ 2)) * F x) =
      ∫ x : ℝ, f x * (1-Real.exp (-((h * x) ^ 2))) * F x := by
  rw [← integral_sub hraw hdamp]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- Gaussian damping removal against a nonnegative bounded spectral density. -/
theorem gaussian_pairing_error_le {f F : ℝ → ℝ}
    (hf : Integrable f) (hF : Continuous F) {M : ℝ}
    (hF0 : ∀ x, 0 ≤ F x) (hFM : ∀ x, F x ≤ M)
    (hmoment : Integrable (fun x => x ^ 2 * |f x|)) (h : ℝ) :
    Integrable (fun x => f x * F x) ∧
    Integrable (fun x => f x * Real.exp (-((h * x) ^ 2)) * F x) ∧
    |(∫ x : ℝ, f x * F x) -
      ∫ x : ℝ, f x * Real.exp (-((h * x) ^ 2)) * F x| ≤
      M * h ^ 2 * ∫ x : ℝ, x ^ 2 * |f x| := by
  have hM : 0 ≤ M := (hF0 0).trans (hFM 0)
  have hraw : Integrable (fun x => f x * F x) :=
    integrable_mul_of_abs_le hf hF (fun x => by rw [abs_of_nonneg (hF0 x)]; exact hFM x)
  have hdamp : Integrable (fun x => f x * Real.exp (-((h * x) ^ 2)) * F x) := by
    have hc : Continuous (fun x => Real.exp (-((h * x) ^ 2)) * F x) := by fun_prop
    have hb : ∀ x, |Real.exp (-((h * x) ^ 2)) * F x| ≤ M := by
      intro x
      rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hF0 x))]
      calc
        _ ≤ 1 * F x := mul_le_mul_of_nonneg_right
          (by have hh := (gaussian_damping_error (h * x)).1; linarith) (hF0 x)
        _ ≤ M := by simpa using hFM x
    simpa only [mul_assoc] using integrable_mul_of_abs_le hf hc hb
  refine ⟨hraw, hdamp, ?_⟩
  rw [← integral_sub hraw hdamp]
  calc
    _ ≤ ∫ x : ℝ, |f x * F x - f x * Real.exp (-((h * x) ^ 2)) * F x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, (M * h ^ 2) * (x ^ 2*|f x|) := by
      apply integral_mono (hraw.sub hdamp).abs (hmoment.const_mul (M * h ^ 2))
      intro x
      change |f x * F x - f x * Real.exp (-((h * x) ^ 2)) * F x| ≤ (M * h ^ 2)*(x ^ 2*|f x|)
      have he := gaussian_damping_error (h * x)
      calc
        _ = |f x| * (1-Real.exp (-((h * x) ^ 2))) * F x := by
          rw [show f x * F x - f x * Real.exp (-((h * x) ^ 2)) * F x =
            f x * (1-Real.exp (-((h * x) ^ 2))) * F x by ring]
          rw [abs_mul, abs_mul, abs_of_nonneg he.1, abs_of_nonneg (hF0 x)]
        _ ≤ |f x| * (h * x) ^ 2 * M := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left he.2 (abs_nonneg _)
          · exact hFM x
          · exact hF0 x
          · positivity
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]

/-- Unconditional quantitative Fourier Gaussian damping removal for the full
actual zero multiset. The constant is uniform in height, width, and test. -/
theorem exists_actual_gaussian_pairing_error :
    ∃ C : ℝ, 0 < C ∧ ∀ T b : ℝ, 9 ≤ T → ∀ f : ℝ → ℝ,
      Integrable f → Integrable (fun a => a ^ 2 * |f a|) →
      Integrable (fun a => f a * formFactor T a) ∧
      Integrable (fun a => f a * Real.exp (-((b * Real.log T * a) ^ 2)) * formFactor T a) ∧
      |(∫ a : ℝ, f a * formFactor T a) -
        ∫ a : ℝ, f a * Real.exp (-((b * Real.log T * a) ^ 2)) * formFactor T a| ≤
        C * b ^ 2 * (Real.log T) ^ 3 * ∫ a : ℝ, a ^ 2 * |f a| := by
  obtain ⟨C,hC,hbound⟩ := MontgomeryLocalMass.exists_formFactor_le_log
  refine ⟨C,hC,?_⟩
  intro T b hT f hf hmoment
  have h := gaussian_pairing_error_le hf (continuous_formFactor T)
    (fun a => formFactor_nonneg (by linarith) a) (fun a => hbound T a hT)
    hmoment (b * Real.log T)
  convert h using 1
  ring

/-- Gaussian damping disappears in the normalized actual pairing whenever
`b(T) ^ 2 * (log T) ^ 3` tends to zero. This is a width condition only. -/
theorem actual_gaussian_pairing_sub_tendsto_zero
    {f : ℝ → ℝ} (hf : Integrable f)
    (hmoment : Integrable (fun a => a ^ 2 * |f a|))
    (b : ℝ → ℝ)
    (hwidth : Filter.Tendsto (fun T => (b T) ^ 2 * (Real.log T) ^ 3)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun T => (∫ a : ℝ, f a * formFactor T a) -
      ∫ a : ℝ, f a * Real.exp (-((b T*Real.log T * a) ^ 2)) * formFactor T a)
      Filter.atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_actual_gaussian_pairing_error
  have hlim : Filter.Tendsto (fun T => C * (b T) ^ 2 * (Real.log T) ^ 3 *
      ∫ a : ℝ, a ^ 2 * |f a|) Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul, mul_assoc] using
      (hwidth.const_mul C).mul_const (∫ a : ℝ, a ^ 2 * |f a|)
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (9 : ℝ)] with T hT
  exact (hbound T (b T) hT f hf hmoment).2.2

set_option maxHeartbeats 600000 in
/-- A concrete width gives an unconditional `1 / log T` error bound. -/
theorem exists_actual_reciprocal_log_pairing_error :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 9 ≤ T → ∀ f : ℝ → ℝ,
      Integrable f → Integrable (fun a => a ^ 2 * |f a|) →
      |(∫ a : ℝ, f a * formFactor T a) -
        ∫ a : ℝ, f a * Real.exp (-((a / Real.log T) ^ 2)) * formFactor T a| ≤
        C / Real.log T * ∫ a : ℝ, a ^ 2 * |f a| := by
  obtain ⟨C,hC,hbound⟩ := exists_actual_gaussian_pairing_error
  refine ⟨C,hC,?_⟩
  intro T hT f hf hm
  have hl : Real.log T ≠ 0 := (Real.log_pos (by linarith : 1 < T)).ne'
  have he (a : ℝ) : (1 / (Real.log T) ^ 2) * Real.log T * a =
      a / Real.log T := by field_simp [hl]
  have hr : C * (1 / (Real.log T) ^ 2) ^ 2 * (Real.log T) ^ 3 =
      C / Real.log T := by field_simp [hl]
  have hh := (hbound T (1 / (Real.log T) ^ 2) hT f hf hm).2.2
  rw [hr] at hh
  simp_rw [he] at hh
  exact hh

/-- The width `b(T)=1/(log T)^2` removes Gaussian Fourier damping without
any unproved spectral or width hypothesis. -/
theorem actual_reciprocal_log_pairing_sub_tendsto_zero
    {f : ℝ → ℝ} (hf : Integrable f)
    (hmoment : Integrable (fun a => a ^ 2 * |f a|)) :
    Filter.Tendsto (fun T => (∫ a : ℝ, f a * formFactor T a) -
      ∫ a : ℝ, f a * Real.exp (-((a / Real.log T) ^ 2)) * formFactor T a)
      Filter.atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_actual_reciprocal_log_pairing_error
  have hi : Filter.Tendsto (fun T : ℝ => (Real.log T)⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hlim : Filter.Tendsto (fun T => C / Real.log T *
      ∫ a : ℝ, a ^ 2 * |f a|) Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      (hi.const_mul C).mul_const (∫ a : ℝ, a ^ 2 * |f a|)
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (9 : ℝ)] with T hT
  exact hbound T hT f hf hmoment

end RiemannResearch.Analysis.MontgomeryGaussianSmoothing
