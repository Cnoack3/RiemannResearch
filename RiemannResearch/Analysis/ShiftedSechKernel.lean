/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryPoisson
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Positive complex-shifted sech smoothing

The kernel is the real part of sech (pi (v + i delta)). We prove its exact
real formula, positivity on |delta| < 1/2, exponential domination,
integrability, exact unit mass, and the complete interval and half-line
integrals. These are unconditional analytic providers for the Montgomery
pair-correlation smoothing route. They do not identify the smoothing with
raw zeta-zero pairs or establish a sampling asymptotic.

Source: the user-provided Montgomery continuation handoff, route A.
The hyperbolic identities used in the real-form reduction are recorded in
DLMF Section 4.35, https://dlmf.nist.gov/4.35. The mass proof is by the
explicit arctangent primitive, with both infinite endpoints retained.
-/

noncomputable section
open MeasureTheory
namespace RiemannResearch.Analysis.ShiftedSech

def kernel (δ v : ℝ) : ℝ :=
  (Complex.cosh ((Real.pi * v : ℝ) + (Real.pi * δ : ℝ) * Complex.I))⁻¹.re

theorem cosh_shift_re (x y : ℝ) :
    (Complex.cosh ((x : ℂ) + (y : ℂ) * Complex.I)).re =
      Real.cosh x * Real.cos y := by
  simp [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    Complex.mul_re, Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]

theorem cosh_shift_im (x y : ℝ) :
    (Complex.cosh ((x : ℂ) + (y : ℂ) * Complex.I)).im =
      Real.sinh x * Real.sin y := by
  simp [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    Complex.mul_re, Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]

theorem kernel_eq (δ v : ℝ) :
    kernel δ v = Real.cosh (Real.pi*v) * Real.cos (Real.pi*δ) /
      ((Real.cosh (Real.pi*v) * Real.cos (Real.pi*δ))^2 +
        (Real.sinh (Real.pi*v) * Real.sin (Real.pi*δ))^2) := by
  unfold kernel
  rw [Complex.inv_re, Complex.normSq_apply, cosh_shift_re, cosh_shift_im]
  ring

theorem cos_pos {δ : ℝ} (hδ : |δ| < 1 / 2) : 0 < Real.cos (Real.pi*δ) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos, (abs_lt.mp hδ).1, (abs_lt.mp hδ).2]

theorem kernel_pos {δ : ℝ} (hδ : |δ| < 1 / 2) (v : ℝ) : 0 < kernel δ v := by
  rw [kernel_eq]
  have h := mul_pos (Real.cosh_pos (Real.pi*v)) (cos_pos hδ)
  exact div_pos h (add_pos_of_pos_of_nonneg (sq_pos_of_pos h) (sq_nonneg _))

theorem kernel_le_reciprocal {δ : ℝ} (hδ : |δ| < 1 / 2) (v : ℝ) :
    kernel δ v ≤ 1 / (Real.cosh (Real.pi*v) * Real.cos (Real.pi*δ)) := by
  rw [kernel_eq]
  have h := mul_pos (Real.cosh_pos (Real.pi*v)) (cos_pos hδ)
  have hd := add_pos_of_pos_of_nonneg (sq_pos_of_pos h)
    (sq_nonneg (Real.sinh (Real.pi*v) * Real.sin (Real.pi*δ)))
  apply (div_le_iff₀ hd).2
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ h).2
  nlinarith [sq_nonneg (Real.sinh (Real.pi*v) * Real.sin (Real.pi*δ))]

theorem reciprocal_cosh_le (x : ℝ) :
    1 / Real.cosh x ≤ 2 * Real.exp (-|x|) := by
  have hc : Real.cosh |x| = Real.cosh x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.cosh_neg]
  have he : Real.exp |x| / 2 ≤ Real.cosh x := by
    rw [← hc, Real.cosh_eq]
    linarith [Real.exp_pos (-|x|)]
  have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
    (by positivity : 0 < Real.exp |x| / 2) he
  calc
    1 / Real.cosh x ≤ 1 / (Real.exp |x| / 2) := hh
    _ = 2 * Real.exp (-|x|) := by rw [Real.exp_neg]; ring

theorem kernel_le_exp {δ : ℝ} (hδ : |δ| < 1 / 2) (v : ℝ) :
    kernel δ v ≤ (2 / Real.cos (Real.pi*δ)) * Real.exp (-(Real.pi*|v|)) := by
  calc
    kernel δ v ≤ 1 / (Real.cosh (Real.pi*v) * Real.cos (Real.pi*δ)) :=
      kernel_le_reciprocal hδ v
    _ = (1 / Real.cos (Real.pi*δ)) * (1 / Real.cosh (Real.pi*v)) := by ring
    _ ≤ (1 / Real.cos (Real.pi*δ)) * (2 * Real.exp (-|Real.pi*v|)) :=
      mul_le_mul_of_nonneg_left (reciprocal_cosh_le _) (by positivity [cos_pos hδ])
    _ = (2 / Real.cos (Real.pi*δ)) * Real.exp (-(Real.pi*|v|)) := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      ring

theorem continuous_kernel {δ : ℝ} (hδ : |δ| < 1 / 2) :
    Continuous (kernel δ) := by
  have heq : kernel δ = fun v => Real.cosh (Real.pi*v) * Real.cos (Real.pi*δ) /
      ((Real.cosh (Real.pi*v) * Real.cos (Real.pi*δ))^2 +
        (Real.sinh (Real.pi*v) * Real.sin (Real.pi*δ))^2) := funext (kernel_eq δ)
  rw [heq]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro v
    have h := mul_pos (Real.cosh_pos (Real.pi*v)) (cos_pos hδ)
    exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos h) (sq_nonneg _))

theorem integrable_kernel {δ : ℝ} (hδ : |δ| < 1 / 2) :
    Integrable (kernel δ) := by
  have he : Integrable (fun v : ℝ => Real.exp (-(Real.pi*|v|))) := by
    have hf := (MontgomeryPoisson.integrable_feature Real.pi 0
      (by simpa using Real.pi_pos)).re
    change Integrable (fun v => (MontgomeryPoisson.feature Real.pi 0 v).re) at hf
    simpa only [MontgomeryPoisson.feature, mul_zero, add_zero,
      ← Complex.ofReal_exp, Complex.ofReal_re] using hf
  apply (he.const_mul (2 / Real.cos (Real.pi*δ))).mono'
    (continuous_kernel hδ).aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_pos (kernel_pos hδ v)]
  exact kernel_le_exp hδ v


theorem kernel_eq_simple (δ v : ℝ) :
    kernel δ v = Real.cosh (Real.pi*v) * Real.cos (Real.pi*δ) /
      (Real.sinh (Real.pi*v)^2 + Real.cos (Real.pi*δ)^2) := by
  rw [kernel_eq]
  congr 1
  rw [mul_pow, mul_pow,
    show Real.cosh (Real.pi*v)^2 = Real.sinh (Real.pi*v)^2 + 1 by
      nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi*v)]]
  calc
    _ = Real.sinh (Real.pi*v)^2 *
      (Real.cos (Real.pi*δ)^2 + Real.sin (Real.pi*δ)^2) +
        Real.cos (Real.pi*δ)^2 := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

def primitive (δ v : ℝ) : ℝ :=
  Real.arctan (Real.sinh (Real.pi*v) / Real.cos (Real.pi*δ)) / Real.pi

theorem hasDerivAt_primitive {δ : ℝ} (hδ : |δ| < 1 / 2) (v : ℝ) :
    HasDerivAt (primitive δ) (kernel δ v) v := by
  have h := ((((hasDerivAt_id v).const_mul Real.pi).sinh.div_const
    (Real.cos (Real.pi*δ))).arctan.div_const Real.pi)
  convert h using 1 <;> try rfl
  rw [kernel_eq_simple]
  have hc := ne_of_gt (cos_pos hδ)
  have hp := Real.pi_ne_zero
  have hd : Real.sinh (Real.pi*v)^2 + Real.cos (Real.pi*δ)^2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (cos_pos hδ)))
  simp only [id_eq]
  field_simp
  <;> ring

theorem tendsto_sinh_atTop : Filter.Tendsto Real.sinh Filter.atTop Filter.atTop :=
  Real.sinh_strictMono.monotone.tendsto_atTop_atTop (fun b => by
    obtain ⟨a, ha⟩ := Real.sinh_surjective b
    exact ⟨a, ha.ge⟩)

theorem tendsto_sinh_atBot : Filter.Tendsto Real.sinh Filter.atBot Filter.atBot :=
  Filter.tendsto_atBot_atBot_of_monotone Real.sinh_strictMono.monotone (fun b => by
    obtain ⟨a, ha⟩ := Real.sinh_surjective b
    exact ⟨a, ha.le⟩)

theorem primitive_atTop {δ : ℝ} (hδ : |δ| < 1 / 2) :
    Filter.Tendsto (primitive δ) Filter.atTop (nhds (1 / 2)) := by
  have hs : Filter.Tendsto (fun v : ℝ => Real.sinh (Real.pi*v) /
      Real.cos (Real.pi*δ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (cos_pos hδ)
      (tendsto_sinh_atTop.comp
        (Filter.Tendsto.const_mul_atTop Real.pi_pos Filter.tendsto_id))
  have h := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hs
  have hd := h.div_const Real.pi
  have hv : Real.pi / 2 / Real.pi = (1 / 2 : ℝ) := by field_simp
  rw [hv] at hd
  exact hd

theorem primitive_atBot {δ : ℝ} (hδ : |δ| < 1 / 2) :
    Filter.Tendsto (primitive δ) Filter.atBot (nhds (-(1 / 2))) := by
  have hs : Filter.Tendsto (fun v : ℝ => Real.sinh (Real.pi*v) /
      Real.cos (Real.pi*δ)) Filter.atBot Filter.atBot :=
    Filter.Tendsto.atBot_div_const (cos_pos hδ)
      (tendsto_sinh_atBot.comp
        (Filter.Tendsto.const_mul_atBot Real.pi_pos Filter.tendsto_id))
  have h := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp hs
  have hd := h.div_const Real.pi
  have hv : -(Real.pi / 2) / Real.pi = -(1 / 2 : ℝ) := by field_simp
  rw [hv] at hd
  exact hd

theorem integral_kernel {δ : ℝ} (hδ : |δ| < 1 / 2) :
    (∫ v : ℝ, kernel δ v) = 1 := by
  have h := integral_of_hasDerivAt_of_tendsto (hasDerivAt_primitive hδ)
    (integrable_kernel hδ) (primitive_atBot hδ) (primitive_atTop hδ)
  norm_num at h ⊢
  exact h


theorem kernel_neg (δ v : ℝ) : kernel δ (-v) = kernel δ v := by
  simp [kernel_eq, mul_neg, Real.cosh_neg, Real.sinh_neg]

theorem kernel_neg_shift (δ v : ℝ) : kernel (-δ) v = kernel δ v := by
  simp [kernel_eq, mul_neg, Real.cos_neg, Real.sin_neg]

theorem intervalIntegral_kernel {δ : ℝ} (hδ : |δ| < 1 / 2) (a b : ℝ) :
    (∫ v : ℝ in a..b, kernel δ v) = primitive δ b - primitive δ a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_primitive hδ v)
    (integrable_kernel hδ).intervalIntegrable

theorem integral_kernel_Ioi {δ : ℝ} (hδ : |δ| < 1 / 2) (a : ℝ) :
    (∫ v : ℝ in Set.Ioi a, kernel δ v) = 1 / 2 - primitive δ a :=
  integral_Ioi_of_hasDerivAt_of_tendsto' (fun v _ => hasDerivAt_primitive hδ v)
    (integrable_kernel hδ).integrableOn (primitive_atTop hδ)

theorem integral_kernel_Iic {δ : ℝ} (hδ : |δ| < 1 / 2) (a : ℝ) :
    (∫ v : ℝ in Set.Iic a, kernel δ v) = primitive δ a + 1 / 2 := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (fun v _ => hasDerivAt_primitive hδ v)
    (integrable_kernel hδ).integrableOn (primitive_atBot hδ) (a := a)
  simpa only [sub_neg_eq_add] using h

end RiemannResearch.Analysis.ShiftedSech
