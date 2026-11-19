/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelFourierMoments
import RiemannResearch.Analysis.GapKernelFourierRecurrence
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! The actual real-line Fourier transform of Gaussian polynomial kernels
with the e^{-2πixu} convention. -/

noncomputable section
open MeasureTheory Real Complex
open scoped FourierTransform Real

namespace RiemannResearch.Analysis.GapKernelFourierGaussian

open GapKernelPolynomial GapKernelObjective GapKernelFourierRecurrence GapKernelFourierMoments

def model (p : List ℤ) (x : ℝ) : ℝ := Real.exp (-Real.pi*x^2) * value p (Real.pi*x^2)

def complexModel (p : List ℤ) (x : ℝ) : ℂ := model p x

private theorem sqDeriv (x : ℝ) : HasDerivAt (fun y : ℝ => Real.pi*y^2) (2*Real.pi*x) x := by
  convert ((hasDerivAt_id x).pow 2).const_mul Real.pi using 1
  all_goals try rfl
  all_goals try simp
  all_goals ring

theorem model_hasDerivAt (p : List ℤ) (x : ℝ) :
    HasDerivAt (model p) (2*Real.pi*x*model (drift p) x) x := by
  have h := ((sqDeriv x).neg.exp).mul ((value_hasDerivAt p _).comp x (sqDeriv x))
  change HasDerivAt (fun y : ℝ => Real.exp (-(Real.pi*y^2)) * value p (Real.pi*y^2))
    (Real.exp (-(Real.pi*x^2)) * -(2*Real.pi*x) * value p (Real.pi*x^2) +
      Real.exp (-(Real.pi*x^2)) * (value (diff p) (Real.pi*x^2) * (2*Real.pi*x))) x at h
  have he : (fun y : ℝ => Real.exp (-(Real.pi*y^2)) * value p (Real.pi*y^2)) = model p := by
    funext y
    simp only [model, neg_mul]
  rw [he] at h
  convert h using 1
  all_goals try rfl
  all_goals simp only [model, value_drift, neg_mul]
  all_goals ring

private theorem secondDeriv (p : List ℤ) (x : ℝ) :
    deriv (deriv (complexModel p)) x = ((-2*Real.pi*model (doubleStep p) x : ℝ) : ℂ) := by
  have hf : deriv (complexModel p) = fun y : ℝ => ((2*Real.pi*y*model (drift p) y : ℝ) : ℂ) := by
    funext y
    exact (model_hasDerivAt p y).ofReal_comp.deriv
  rw [hf]
  have h := (((hasDerivAt_id x).const_mul (2*Real.pi)).mul (model_hasDerivAt (drift p) x)).ofReal_comp.deriv
  change deriv (fun y : ℝ => ((2*Real.pi*y*model (drift p) y : ℝ) : ℂ)) x = _ at h
  rw [h]
  apply congrArg (fun z : ℝ => (z : ℂ))
  simp only [model, value_doubleStep, id_eq, mul_one]
  ring

theorem weighted_integrable (p : List ℤ) (k : ℕ) :
    Integrable (fun x : ℝ => x^k * model p x) := by
  induction p generalizing k with
  | nil => simp [model, value, integrable_zero]
  | cons a p ih =>
    have hg : Integrable (fun x : ℝ => x^k*Real.exp (-Real.pi*x^2)) := by
      simpa only [Real.rpow_natCast] using (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos
        (show (-1 : ℝ) < (k : ℝ) by have : 0 ≤ (k : ℝ) := Nat.cast_nonneg k; linarith))
    have h := (hg.const_mul (a : ℝ)).add ((ih (k+2)).const_mul Real.pi)
    apply h.congr
    filter_upwards [] with x
    simp only [model, value, Pi.add_apply, pow_add]
    ring

private theorem three_moments (p : List ℤ) :
    Integrable (complexModel p) ∧ Integrable (mulVariable (complexModel p)) ∧
      Integrable (mulVariable (mulVariable (complexModel p))) := by
  have hw (k : ℕ) : Integrable (fun x : ℝ => ((x^k*model p x : ℝ) : ℂ)) :=
    (weighted_integrable p k).ofReal
  refine ⟨(hw 0).congr ?_, (hw 1).congr ?_, (hw 2).congr ?_⟩
  all_goals filter_upwards [] with x
  all_goals simp [complexModel, mulVariable, pow_two, mul_assoc]

private theorem transform_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (f+g) = 𝓕 f + 𝓕 g := by
  funext u
  simp only [Real.fourier_eq, Pi.add_apply, smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff u).2 hf)
    ((Real.fourierIntegral_convergent_iff u).2 hg)]

theorem transform_unitGaussian : 𝓕 (complexModel [1]) = complexModel [1] := by
  have h := fourier_gaussian_pi (b := 1) (by norm_num)
  have he : complexModel [1] = fun x : ℝ => Complex.exp (-(Real.pi : ℂ)*(x : ℂ)^2) := by
    funext x
    simp [complexModel, model, value, Complex.ofReal_exp]
  simpa only [he, mul_one, div_one, Complex.one_cpow, one_mul] using h

/-- The arithmetic transport controls the genuine Fourier transform,
including its normalizing power of two. -/
theorem fourier_transport (p : List ℤ) :
    𝓕 (complexModel p) = fun u => ((2 : ℂ)^p.length)⁻¹ * complexModel (transport p) u := by
  induction p with
  | nil =>
    funext u
    simp [Real.fourier_real_eq_integral_exp_smul, complexModel, model, value, transport]
  | cons a p ih =>
    have hs : complexModel (a :: p) = (fun x : ℝ => (a : ℂ) * complexModel [1] x)
        + fun x : ℝ => (Real.pi : ℂ) * (x : ℂ)^2 * complexModel p x := by
      funext x
      simp only [Pi.add_apply, complexModel, model, value, Int.cast_one, mul_zero, add_zero,
        mul_one]
      push_cast
      ring
    obtain ⟨hf, hxf, hx2f⟩ := three_moments p
    have hquad : Integrable (fun x : ℝ => (Real.pi : ℂ) * (x : ℂ)^2 * complexModel p x) := by
      convert hx2f.const_mul (Real.pi : ℂ) using 1
      funext x
      simp only [mulVariable]
      ring
    rw [hs, transform_add ((three_moments [1]).1.const_mul (a : ℂ)) hquad,
      transform_const_mul, transform_unitGaussian]
    funext u
    simp only [Pi.add_apply]
    rw [transform_mul_quadratic hf hxf hx2f, ih, deriv_const_mul_field', deriv_const_mul_field,
      secondDeriv]
    simp only [transport, complexModel, model, value_add, value, mul_zero, add_zero,
      List.length_cons]
    push_cast
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [pow_succ]
    field_simp [hp]
    ring

theorem fourier_eq_of_transport {p q : List ℤ}
    (h : transport p = scale (2^p.length) q) : 𝓕 (complexModel p) = complexModel q := by
  rw [fourier_transport, h]
  funext u
  simp only [complexModel, model, value_scale]
  push_cast
  field_simp

end RiemannResearch.Analysis.GapKernelFourierGaussian
