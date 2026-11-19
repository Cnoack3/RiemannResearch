/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelFourierGaussian
import RiemannResearch.Analysis.GapKernelFourierModel
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Dilation and normalization identify the real cosine integral of a
Gaussian-polynomial test with the signed Fourier model used for gaps. -/

noncomputable section
open MeasureTheory Real Complex
open scoped FourierTransform Real

namespace RiemannResearch.Analysis.GapKernelFourierGaussian

open GapKernelFourierMoments GapKernelFourierRecurrence GapKernelPolynomial

theorem fourier_comp_div (f : ℝ → ℂ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    𝓕 (fun x => f (x/s)) u = (s : ℂ) * 𝓕 f (s*u) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  let g := fun y : ℝ => Complex.exp (((-2*Real.pi*y*(s*u) : ℝ) : ℂ)*Complex.I)*f y
  have he : (fun x : ℝ => Complex.exp (((-2*Real.pi*x*u : ℝ) : ℂ)*Complex.I)*f (x/s)) =
      fun x : ℝ => g (x/s) := by
    funext x
    dsimp [g]
    rw [show -2*Real.pi*(x/s)*(s*u)=-2*Real.pi*x*u by field_simp <;> ring]
  rw [he, Measure.integral_comp_div g s, abs_of_pos hs]
  simp only [Complex.real_smul, g]

theorem cosine_eq_re_transform {f : ℝ → ℝ} (hf : Integrable f) (u : ℝ) :
    (∫ x : ℝ, f x * Real.cos (2 * Real.pi * x * u)) =
      (𝓕 (fun x => (f x : ℂ)) u).re := by
  rw [Real.fourier_eq]
  change _ = RCLike.re (∫ x : ℝ, Real.fourierChar (-inner ℝ x u) • (f x : ℂ))
  rw [← integral_re ((Real.fourierIntegral_convergent_iff u).2 hf.ofReal)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Circle.smul_def, Real.fourierChar_apply, Real.inner_apply, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  congr 1
  rw [show Real.pi * (-(u*x)*2) = -(u*(x*(Real.pi*2))) by ring, Real.cos_neg]

def normalizedTest (p q : List ℤ) (s x : ℝ) : ℝ := model p (x/s)/(s*value q 0)

theorem normalized_fourier_cosine {p q : List ℤ} {s : ℝ} (hs : 0 < s)
    (hq : 0 < value q 0) (h : transport p = scale (2^p.length) q) (u : ℝ) :
    (∫ x : ℝ, normalizedTest p q s x * Real.cos (2 * Real.pi*x*u)) = fourierModel s q u := by
  have hi : Integrable (model p) := by simpa only [pow_zero, one_mul] using weighted_integrable p 0
  have hi' : Integrable (normalizedTest p q s) := by
    apply ((hi.comp_div hs.ne').const_mul ((s*value q 0)⁻¹)).congr
    filter_upwards [] with x
    simp only [normalizedTest, div_eq_inv_mul]
  rw [cosine_eq_re_transform hi']
  have hcast : (fun x : ℝ => (normalizedTest p q s x : ℂ)) =
      fun x : ℝ => ((s*value q 0 : ℝ) : ℂ)⁻¹*complexModel p (x/s) := by
    funext x
    simp [normalizedTest, complexModel, div_eq_inv_mul]
  rw [hcast, transform_const_mul]
  change (((s*value q 0 : ℝ) : ℂ)⁻¹ * 𝓕 (fun x : ℝ => complexModel p (x/s)) u).re = _
  rw [fourier_comp_div (complexModel p) hs u, fourier_eq_of_transport h]
  simp only [complexModel, model, fourierModel, ← Complex.ofReal_mul, ← Complex.ofReal_inv,
    Complex.ofReal_re]
  have he : -(Real.pi*(s*u)^2) = -Real.pi*(s*u)^2 := by ring
  rw [he]
  field_simp [hs.ne', hq.ne'] <;> ring

end RiemannResearch.Analysis.GapKernelFourierGaussian
