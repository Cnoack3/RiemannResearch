/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GaussianPolynomialFourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fourier inversion with the repository normalization

The normalized transform is defined in GaussianPolynomialFourier. The results
here apply to arbitrary complex-valued functions on the real line. They reconcile
the frequency variable and Jacobian with Mathlib, transfer integrability, and
apply real Fourier inversion at continuity points.

Source for normalization and the intended actual-zeta consumer:
[GaussianActualZetaExplicitFormula20261029.md, Sections 1--3]
(https://github.com/Cnoack3/RiemannResearch/blob/933fb43028951dd503c7ec2a14808f365bad7e72/RiemannResearch/RH/GaussianActualZetaExplicitFormula20261029.md).
Proof strategy: Mathlib.Analysis.Fourier.Inversion, in particular
MeasureTheory.Integrable.fourierInv_fourier_eq, with u = 2πv.
No Gaussian, zeta, contour, or RH hypothesis is used in the general inversion lemma.
-/

open MeasureTheory
open scoped FourierTransform
noncomputable section

namespace RiemannResearch.Analysis.GaussianPolynomialFourier

/-- Exact frequency-scale conversion, with the reciprocal normalization solved for Mathlib. -/
theorem fourier_eq_scaled_transform (f : ℝ → ℂ) (v : ℝ) :
    𝓕 f v = (2 * Real.pi : ℂ) * transform f ((2*Real.pi)*v) := by
  rw [transform_eq_fourier]
  have hs : (2*Real.pi)*v/(2*Real.pi) = v := by field_simp
  rw [hs]
  field_simp

/-- Substitution u = 2πv converts the inverse kernel exactly, including the Jacobian. -/
theorem inverse_integral_eq_fourierInv (f : ℝ → ℂ) (x : ℝ) :
    (∫ u : ℝ, Complex.exp (Complex.I*x*u) * transform f u) = 𝓕⁻ (𝓕 f) x := by
  let k : ℝ → ℂ := fun u => Complex.exp (Complex.I*x*u) * transform f u
  have hs := Measure.integral_comp_mul_left k (2*Real.pi)
  have hval : (∫ v : ℝ, k ((2*Real.pi)*v)) =
      (2*Real.pi : ℂ)⁻¹ * 𝓕⁻ (𝓕 f) x := by
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only [k]
    rw [transform_eq_fourier]
    have hv : (2*Real.pi)*v/(2*Real.pi) = v := by field_simp
    rw [hv]
    simp only [smul_eq_mul]
    push_cast
    have he : Complex.I * (x : ℂ) * (2 * (Real.pi : ℂ) * (v : ℂ)) =
        (-2 * (Real.pi : ℂ) * (v : ℂ) * -(x : ℂ)) * Complex.I := by ring
    rw [he]
    ring
  rw [hval, abs_of_pos (inv_pos.mpr (by positivity : 0 < 2*Real.pi)),
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat] at hs
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (show (2:ℝ)*Real.pi ≠ 0 by positivity)
  exact (mul_left_cancel₀ (inv_ne_zero hp) hs).symm

/-- Integrability passes from the repository-normalized transform to Mathlib's transform. -/
theorem integrable_fourier_of_integrable_transform {f : ℝ → ℂ}
    (hf : Integrable (transform f)) : Integrable (𝓕 f) := by
  have hs := (integrable_comp_mul_left_iff (transform f)
    (show (2:ℝ)*Real.pi ≠ 0 by positivity)).mpr hf
  have hc := hs.const_mul (2*Real.pi : ℂ)
  simpa only [← fourier_eq_scaled_transform] using hc


/-- Real inversion for the repository normalization at every continuity point. -/
theorem inverse_integral_eq {f : ℝ → ℂ} (hf : Integrable f)
    (hft : Integrable (transform f)) {x : ℝ} (hx : ContinuousAt f x) :
    (∫ u : ℝ, Complex.exp (Complex.I*x*u) * transform f u) = f x := by
  rw [inverse_integral_eq_fourierInv]
  exact hf.fourierInv_fourier_eq (integrable_fourier_of_integrable_transform hft) hx

end RiemannResearch.Analysis.GaussianPolynomialFourier
