/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Real Complex
open scoped FourierTransform Real

namespace RiemannResearch.Analysis.GapKernelFourierMoments

def mulVariable (f : ℝ → ℂ) (x : ℝ) : ℂ := (x : ℂ) * f x

theorem transform_const_mul (k : ℂ) (f : ℝ → ℂ) :
    𝓕 (fun x => k*f x) = fun u => k * 𝓕 f u := by
  funext u
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem deriv_transform {f : ℝ → ℂ} (hf : Integrable f)
    (hxf : Integrable (mulVariable f)) :
    deriv (𝓕 f) = fun u => (-2 * (Real.pi : ℂ) * Complex.I) * 𝓕 (mulVariable f) u := by
  have hxf' : Integrable (fun x : ℝ => x • f x) := by
    convert hxf using 1
    funext x
    simp only [Complex.real_smul, mulVariable]
  rw [Real.deriv_fourier hf hxf', ← transform_const_mul]
  congr 1
  funext x
  simp only [smul_eq_mul, mulVariable]
  ring

/-- Taking two frequency derivatives gives the exact transform of
multiplication by π x² under the e^{-2 π i x u} convention. -/
theorem transform_mul_quadratic {f : ℝ → ℂ} (hf : Integrable f)
    (hxf : Integrable (mulVariable f)) (hx2f : Integrable (mulVariable (mulVariable f))) (u : ℝ) :
    𝓕 (fun x : ℝ => (Real.pi : ℂ) * (x : ℂ)^2 * f x) u =
      -(1 / (4 * (Real.pi : ℂ))) * deriv (deriv (𝓕 f)) u := by
  have h1 := deriv_transform hf hxf
  have h2 := deriv_transform hxf hx2f
  have hc : (fun x : ℝ => (Real.pi : ℂ) * (x : ℂ)^2 * f x) =
      fun x => (Real.pi : ℂ)*mulVariable (mulVariable f) x := by
    funext x
    simp only [mulVariable]
    ring
  rw [hc, transform_const_mul, h1, deriv_const_mul_field, h2]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc2 : (-2 * (Real.pi : ℂ) * Complex.I) * (-2 * (Real.pi : ℂ) * Complex.I) =
      -4 * (Real.pi : ℂ)^2 := by
    calc
      _ = 4 * (Real.pi : ℂ)^2 * Complex.I^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [← mul_assoc (-2 * (Real.pi : ℂ) * Complex.I), hc2]
  field_simp [hp] <;> ring

end RiemannResearch.Analysis.GapKernelFourierMoments
