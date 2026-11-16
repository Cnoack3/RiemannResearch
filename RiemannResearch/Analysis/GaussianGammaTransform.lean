/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GaussianVerticalLaplace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Gaussian vertical transforms with an arbitrary Gamma shift

For complex `a,z`, positive `Delta`, and `re a + c > 0`, this module evaluates
the integral of `exp((s-l-iu)^2/Delta^2) Gamma(a+s) exp(s*z)` over `s=c+it`.
Euler's integral and the complex Gaussian transform give an exact integral
on the positive real axis. The product-space norm factors exactly, so joint
absolute integrability and Fubini are proved before the interchange.

The Euler integrand is integrable for every complex `a,z`: the auxiliary
abscissa can be chosen as `1-re a`. The vertical transform is independent
of its abscissa throughout `re a + c > 0`.

Sources for the ingredients: Mathlib's `Complex.Gamma_eq_integral`,
`Complex.GammaIntegral_convergent`, and `Complex.gaussian_vertical_laplace_integral`.
The RH consumer is the scalar transform in Baluyot's 2017 thesis, Section 3.3
and Lemma 3.1.7 (proof strategy, not an assertion of its ray-rotation formula):
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The arbitrary complex shift/frequency formulation is a reusable extension
of the Euler-integral step in the supplied continuation agenda.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace Complex

/-- The actual Euler and vertical-Gaussian product before Fubini. -/
def gaussianGammaEulerKernel (a z : ℂ) (c l Δ u x t : ℝ) : ℂ :=
  ((Real.exp (-x) : ℂ) * (x : ℂ) ^ (a + (c : ℂ) + I * t - 1)) *
    exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
      exp (((c : ℂ) + I * t) * z)

/-- Exact factorization of the joint norm on the positive Euler axis. -/
theorem gaussianGammaEulerKernel_norm (a z : ℂ) (c l Δ u t : ℝ)
    {x : ℝ} (hx : 0 < x) :
    ‖gaussianGammaEulerKernel a z c l Δ u x t‖ =
      (Real.exp (-x) * x ^ (a.re + c - 1)) *
        ‖exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
          exp (((c : ℂ) + I * t) * z)‖ := by
  simp [gaussianGammaEulerKernel, norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp, mul_assoc]

/-- Joint absolute integrability, proved from the separated norm factors. -/
theorem gaussianGammaEulerKernel_integrable (a z : ℂ) (c l u : ℝ)
    {Δ : ℝ} (hΔ : 0 < Δ) (ha : 0 < a.re + c) :
    Integrable (fun p : ℝ × ℝ => gaussianGammaEulerKernel a z c l Δ u p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hG := gaussian_vertical_laplace_integrable c l u hΔ z
  have hm : Measurable (fun p : ℝ × ℝ =>
      gaussianGammaEulerKernel a z c l Δ u p.1 p.2) := by
    unfold gaussianGammaEulerKernel
    fun_prop
  refine ((Real.GammaIntegral_convergent ha).mul_prod hG.norm).mono'
    hm.aestronglyMeasurable ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem measurableSet_Ioi)] with p hp
  exact le_of_eq (gaussianGammaEulerKernel_norm a z c l Δ u p.2 hp)

/-- Integrating the Euler variable recovers the actual Gamma factor. -/
theorem integral_gaussianGammaEulerKernel_left (a z : ℂ) (c l Δ u t : ℝ)
    (ha : 0 < a.re + c) :
    (∫ x : ℝ in Ioi 0, gaussianGammaEulerKernel a z c l Δ u x t) =
      exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
        Gamma (a + (c : ℂ) + I * t) * exp (((c : ℂ) + I * t) * z) := by
  have hp : 0 < (a + (c : ℂ) + I * t).re := by simpa using ha
  unfold gaussianGammaEulerKernel
  rw [integral_mul_const, integral_mul_const, ← GammaIntegral, ← Gamma_eq_integral hp]
  ring

/-- Factorization isolating the Gaussian with its shifted complex frequency. -/
theorem gaussianGammaEulerKernel_factor (a z : ℂ) (c l Δ u t : ℝ)
    {x : ℝ} (hx : 0 < x) :
    gaussianGammaEulerKernel a z c l Δ u x t =
      ((Real.exp (-x) : ℂ) * (x : ℂ) ^ (a - 1)) *
        (exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
          exp (((c : ℂ) + I * t) * (z + log (x : ℂ)))) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hp : (x : ℂ) ^ (a + (c : ℂ) + I * t - 1) =
      (x : ℂ) ^ (a - 1) * exp (((c : ℂ) + I * t) * log (x : ℂ)) := by
    simp only [cpow_def_of_ne_zero hx', ← exp_add]
    congr 1
    ring
  rw [gaussianGammaEulerKernel, hp, mul_add, exp_add]
  ring

/-- Integrating the vertical variable evaluates the inner complex Gaussian. -/
theorem integral_gaussianGammaEulerKernel_right (a z : ℂ) (c l u : ℝ)
    {Δ x : ℝ} (hΔ : 0 < Δ) (hx : 0 < x) :
    (∫ t : ℝ, gaussianGammaEulerKernel a z c l Δ u x t) =
      ((Δ * Real.sqrt Real.pi : ℝ) : ℂ) *
        (((Real.exp (-x) : ℂ) * (x : ℂ) ^ (a - 1)) *
          exp (((l : ℂ) + I * u) * (z + log (x : ℂ)) -
            (Δ : ℂ)^2 * (z + log (x : ℂ))^2 / 4)) := by
  simp_rw [gaussianGammaEulerKernel_factor a z c l Δ u _ hx]
  rw [integral_const_mul, gaussian_vertical_laplace_integral c l u hΔ]
  ring

/-- Absolute integrability for arbitrary complex Gamma shift and frequency. -/
theorem gaussian_gamma_vertical_laplace_integrable (a z : ℂ) (c l u : ℝ)
    {Δ : ℝ} (hΔ : 0 < Δ) (ha : 0 < a.re + c) :
    Integrable (fun t : ℝ =>
      exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
        Gamma (a + (c : ℂ) + I * t) * exp (((c : ℂ) + I * t) * z)) := by
  apply (gaussianGammaEulerKernel_integrable a z c l u hΔ ha).integral_prod_right.congr
  filter_upwards [] with t
  exact integral_gaussianGammaEulerKernel_left a z c l Δ u t ha

/-- Exact Gamma-weighted Gaussian transform, with product-space Fubini proved. -/
theorem gaussian_gamma_vertical_laplace_integral (a z : ℂ) (c l u : ℝ)
    {Δ : ℝ} (hΔ : 0 < Δ) (ha : 0 < a.re + c) :
    (∫ t : ℝ,
      exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
        Gamma (a + (c : ℂ) + I * t) * exp (((c : ℂ) + I * t) * z)) =
      ((Δ * Real.sqrt Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ in Ioi 0,
          ((Real.exp (-x) : ℂ) * (x : ℂ) ^ (a - 1)) *
            exp (((l : ℂ) + I * u) * (z + log (x : ℂ)) -
              (Δ : ℂ)^2 * (z + log (x : ℂ))^2 / 4)) := by
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ in Ioi 0,
        gaussianGammaEulerKernel a z c l Δ u x t := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact (integral_gaussianGammaEulerKernel_left a z c l Δ u t ha).symm
    _ = ∫ x : ℝ in Ioi 0, ∫ t : ℝ,
        gaussianGammaEulerKernel a z c l Δ u x t :=
      (integral_integral_swap (gaussianGammaEulerKernel_integrable a z c l u hΔ ha)).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact integral_gaussianGammaEulerKernel_right a z c l u hΔ hx

/-- The evaluated Euler integral converges for all complex shifts and frequencies. -/
theorem gaussian_gamma_euler_integrable (a z : ℂ) (l u : ℝ)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    IntegrableOn (fun x : ℝ =>
      ((Real.exp (-x) : ℂ) * (x : ℂ) ^ (a - 1)) *
        exp (((l : ℂ) + I * u) * (z + log (x : ℂ)) -
          (Δ : ℂ)^2 * (z + log (x : ℂ))^2 / 4)) (Ioi 0) := by
  let C : ℂ := ((Δ * Real.sqrt Real.pi : ℝ) : ℂ)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast (mul_ne_zero hΔ.ne' (Real.sqrt_pos.mpr Real.pi_pos).ne')
  have hc : 0 < a.re + (1 - a.re) := by linarith
  have hi := (gaussianGammaEulerKernel_integrable a z (1 - a.re) l u hΔ hc).integral_prod_left
  have hh : Integrable (fun x : ℝ => C *
      (((Real.exp (-x) : ℂ) * (x : ℂ) ^ (a - 1)) *
        exp (((l : ℂ) + I * u) * (z + log (x : ℂ)) -
          (Δ : ℂ)^2 * (z + log (x : ℂ))^2 / 4))) (volume.restrict (Ioi 0)) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact integral_gaussianGammaEulerKernel_right a z (1 - a.re) l u hΔ hx
  have h := hh.const_mul C⁻¹
  simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h

/-- No upper bound on either abscissa is needed. -/
theorem gaussian_gamma_vertical_laplace_abscissa_independent (a z : ℂ)
    (c d l u : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hc : 0 < a.re + c) (hd : 0 < a.re + d) :
    (∫ t : ℝ,
      exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
        Gamma (a + (c : ℂ) + I * t) * exp (((c : ℂ) + I * t) * z)) =
    (∫ t : ℝ,
      exp ((((d : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
        Gamma (a + (d : ℂ) + I * t) * exp (((d : ℂ) + I * t) * z)) := by
  rw [gaussian_gamma_vertical_laplace_integral a z c l u hΔ hc,
    gaussian_gamma_vertical_laplace_integral a z d l u hΔ hd]

end Complex
