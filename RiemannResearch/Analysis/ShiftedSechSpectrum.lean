/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ShiftedSechKernel

/-! # Integrable frequency profile for shifted sech smoothing

The frequency profile cosh(delta*u)/cosh(u/2) is strictly positive,
bounded by one on |delta| <= 1/2, and bounded by an explicit exponential
with decay rate 1/2 - |delta|. It is integrable in the open strip.
The profile and complex averaging identities support the Fourier
transform provider; this module alone does not assert that transform.

Source: user-provided Montgomery continuation handoff, route A;
elementary hyperbolic identities in https://dlmf.nist.gov/4.35.
-/

noncomputable section
open MeasureTheory
namespace RiemannResearch.Analysis.ShiftedSech

def spectrum (δ u : ℝ) : ℝ := Real.cosh (δ*u) / Real.cosh (u/2)

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

theorem spectrum_pos (δ u : ℝ) : 0 < spectrum δ u :=
  div_pos (Real.cosh_pos _) (Real.cosh_pos _)

theorem spectrum_le_exp (δ u : ℝ) :
    spectrum δ u ≤ 2 * Real.exp (-((1 / 2 - |δ|)*|u|)) := by
  calc
    spectrum δ u = Real.cosh (δ*u) * (1 / Real.cosh (u/2)) := by
      unfold spectrum; ring
    _ ≤ Real.exp |δ*u| * (2 * Real.exp (-|u/2|)) :=
      mul_le_mul (cosh_le_exp_abs _) (reciprocal_cosh_le _)
        (by positivity) (Real.exp_pos _).le
    _ = 2 * Real.exp (-((1 / 2 - |δ|)*|u|)) := by
      rw [abs_mul, abs_div]
      norm_num
      rw [show Real.exp (|δ| * |u|) * (2 * Real.exp (-(|u|/2))) =
        2 * (Real.exp (|δ| * |u|) * Real.exp (-(|u|/2))) by ring, ← Real.exp_add]
      congr 2
      ring

theorem continuous_spectrum (δ : ℝ) : Continuous (spectrum δ) := by
  unfold spectrum
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro u; exact ne_of_gt (Real.cosh_pos _)

theorem integrable_spectrum {δ : ℝ} (hδ : |δ| < 1 / 2) :
    Integrable (spectrum δ) := by
  have ha : 0 < 1 / 2 - |δ| := by linarith
  have he : Integrable (fun v : ℝ => Real.exp (-((1 / 2 - |δ|)*|v|))) := by
    have hf := (MontgomeryPoisson.integrable_feature (1 / 2 - |δ|) 0
      (by simpa using ha)).re
    change Integrable (fun v => (MontgomeryPoisson.feature (1 / 2 - |δ|) 0 v).re) at hf
    simpa only [MontgomeryPoisson.feature, mul_zero, add_zero,
      ← Complex.ofReal_exp, Complex.ofReal_re] using hf
  apply (he.const_mul 2).mono' (continuous_spectrum δ).aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_pos (spectrum_pos δ u)]
  exact spectrum_le_exp δ u


theorem spectrum_le_one {δ : ℝ} (hδ : |δ| ≤ 1 / 2) (u : ℝ) :
    spectrum δ u ≤ 1 := by
  apply (div_le_one (Real.cosh_pos _)).2
  apply Real.cosh_le_cosh.mpr
  rw [abs_mul, abs_div]
  norm_num
  nlinarith [abs_nonneg u]

theorem spectrum_neg (δ u : ℝ) : spectrum δ (-u) = spectrum δ u := by
  simp [spectrum, mul_neg, neg_div, Real.cosh_neg]

theorem spectrum_zero (δ : ℝ) : spectrum δ 0 = 1 := by
  simp [spectrum]

theorem ofReal_kernel_eq_average (δ v : ℝ) :
    (kernel δ v : ℂ) =
      ((Complex.cosh ((Real.pi*v : ℝ) + (Real.pi*δ : ℝ)*Complex.I))⁻¹ +
       (Complex.cosh ((Real.pi*v : ℝ) - (Real.pi*δ : ℝ)*Complex.I))⁻¹) / 2 := by
  rw [kernel, Complex.re_eq_add_conj]
  simp [map_inv₀, ← Complex.cosh_conj, sub_eq_add_neg]


end RiemannResearch.Analysis.ShiftedSech
