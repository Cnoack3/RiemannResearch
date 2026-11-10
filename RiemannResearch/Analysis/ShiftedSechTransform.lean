/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ShiftedSechSpectrum
import RiemannResearch.Analysis.SechLaplaceTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Fourier transform of the positive shifted sech kernel

For |delta| < 1/2, the exact positive-frequency transform is
integral kernel(delta,v) exp(i*u*v) dv = cosh(delta*u)/cosh(u/2).
The proof evaluates the transform of the frequency profile using the
Beta-integral Laplace provider, then applies Fourier inversion.
Both sides are proved integrable. No RH or sampling hypothesis occurs.

Source: user-provided Montgomery continuation handoff, route A.2.
The analytic input is proved in SechLaplaceTransform.lean, with the
Beta and Gamma references documented there.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace RiemannResearch.Analysis.ShiftedSech

def profile (δ x : ℝ) : ℂ := (spectrum δ (2 * Real.pi * x) : ℝ)

theorem continuous_profile (δ : ℝ) : Continuous (profile δ) := by
  exact Complex.continuous_ofReal.comp ((continuous_spectrum δ).comp (by fun_prop))

theorem integrable_profile {δ : ℝ} (hδ : |δ| < 1 / 2) : Integrable (profile δ) := by
  have h := (integrable_comp_mul_left_iff (spectrum δ)
    (by positivity : 2 * Real.pi ≠ 0)).mpr (integrable_spectrum hδ)
  exact h.ofReal

theorem profile_neg (δ x : ℝ) : profile δ (-x) = profile δ x := by
  simp [profile, mul_neg, spectrum_neg]

def laplaceAtom (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (z * ((Real.pi*x : ℝ) : ℂ)) / (Real.cosh (Real.pi*x) : ℂ)

theorem scaled_laplace
    (z : ℂ) (hz : |z.re| < 1) :
    (∫ x : ℝ, laplaceAtom z x) = (Complex.cos ((Real.pi:ℂ)*z/2))⁻¹ := by
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => Complex.exp (z*(x:ℂ)) / (Real.cosh x : ℂ)) Real.pi
  rw [SechLaplace.integral_exp_div_cosh z hz] at h
  change (∫ x : ℝ, laplaceAtom z x) = _ at h
  rw [h]
  rw [abs_of_pos (inv_pos.mpr Real.pi_pos), Complex.real_smul]
  push_cast
  field_simp

theorem laplaceAtom_integrable
    (z : ℂ) (hz : |z.re| < 1) : Integrable (laplaceAtom z) :=
  (integrable_comp_mul_left_iff _ Real.pi_ne_zero).mpr (SechLaplace.integrable_exp_div_cosh z hz)

theorem profile_phase_expansion (δ v x : ℝ) :
    Complex.exp ((-2*Real.pi*x*v : ℝ)*Complex.I) * profile δ x =
      (laplaceAtom (2*(δ:ℂ)-2*(v:ℂ)*Complex.I) x +
       laplaceAtom (-2*(δ:ℂ)-2*(v:ℂ)*Complex.I) x) / 2 := by
  unfold profile spectrum laplaceAtom
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
  push_cast
  rw [Complex.cosh]
  have h1 : ((-2*Real.pi*x*v : ℝ):ℂ)*Complex.I +
      ((δ*(2*Real.pi*x):ℝ):ℂ) =
      (2*(δ:ℂ)-2*(v:ℂ)*Complex.I)*((Real.pi*x:ℝ):ℂ) := by
    push_cast; ring
  have h2 : ((-2*Real.pi*x*v : ℝ):ℂ)*Complex.I -
      ((δ*(2*Real.pi*x):ℝ):ℂ) =
      (-2*(δ:ℂ)-2*(v:ℂ)*Complex.I)*((Real.pi*x:ℝ):ℂ) := by
    push_cast; ring
  have e1 := congrArg Complex.exp h1
  have e2 := congrArg Complex.exp h2
  rw [Complex.exp_add] at e1
  rw [sub_eq_add_neg, Complex.exp_add] at e2
  push_cast at e1 e2
  calc
    _ = (Complex.exp (((-2*Real.pi*x*v : ℝ):ℂ)*Complex.I) *
         Complex.exp (((δ*(2*Real.pi*x):ℝ):ℂ)) +
        Complex.exp (((-2*Real.pi*x*v : ℝ):ℂ)*Complex.I) *
         Complex.exp (-((δ*(2*Real.pi*x):ℝ):ℂ))) /
          ((Real.cosh (Real.pi*x):ℂ)*2) := by push_cast; ring
    _ = _ := by push_cast; rw [e1, e2]; ring

theorem fourier_profile
    {δ : ℝ} (hδ : |δ| < 1 / 2) (v : ℝ) :
    𝓕 (profile δ) v = (kernel δ v : ℂ) := by
  have hp : |(2*(δ:ℂ)-2*(v:ℂ)*Complex.I).re| < 1 := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    linarith
  have hm : |(-2*(δ:ℂ)-2*(v:ℂ)*Complex.I).re| < 1 := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    linarith
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, profile_phase_expansion]
  rw [integral_div, integral_add (laplaceAtom_integrable _ hp)
    (laplaceAtom_integrable _ hm),
    scaled_laplace _ hp, scaled_laplace _ hm,
    ofReal_kernel_eq_average]
  have hc1 : Complex.cos ((Real.pi:ℂ)*(2*(δ:ℂ)-2*(v:ℂ)*Complex.I)/2) =
      Complex.cosh ((Real.pi*v:ℝ) + (Real.pi*δ:ℝ)*Complex.I) := by
    rw [← Complex.cosh_mul_I]
    congr 1
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hc2 : Complex.cos ((Real.pi:ℂ)*(-2*(δ:ℂ)-2*(v:ℂ)*Complex.I)/2) =
      Complex.cosh ((Real.pi*v:ℝ) - (Real.pi*δ:ℝ)*Complex.I) := by
    rw [← Complex.cosh_mul_I]
    congr 1
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [hc1, hc2]

theorem inverse_kernel
    {δ : ℝ} (hδ : |δ| < 1 / 2)
    (x : ℝ) :
    𝓕⁻ (fun v => (kernel δ v : ℂ)) x = profile δ x := by
  have hh : 𝓕 (profile δ) = fun v => (kernel δ v : ℂ) := funext (fourier_profile hδ)
  have hI : Integrable (𝓕 (profile δ)) := by
    rw [hh]
    exact (integrable_kernel hδ).ofReal
  have hi := congrFun ((continuous_profile δ).fourierInv_fourier_eq
    (integrable_profile hδ) hI) x
  rwa [hh] at hi


theorem integral_kernel_phase
    {δ : ℝ} (hδ : |δ| < 1 / 2)
    (u : ℝ) :
    (∫ v : ℝ, (kernel δ v : ℂ) * Complex.exp ((u*v : ℝ)*Complex.I)) =
      (spectrum δ u : ℂ) := by
  have hi := inverse_kernel hδ (u / (2 * Real.pi))
  rw [Real.fourierInv_eq'] at hi
  simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial, smul_eq_mul] at hi
  have hscale : 2 * Real.pi * (u / (2 * Real.pi)) = u := by field_simp
  have harg (v : ℝ) : 2 * Real.pi * (v * (u / (2 * Real.pi))) = u*v := by
    field_simp
  simp_rw [harg] at hi
  dsimp only [profile] at hi
  rw [hscale] at hi
  simpa only [mul_comm] using hi

end RiemannResearch.Analysis.ShiftedSech
