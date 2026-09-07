import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential cost of a remote Laplace signature

Analytic formalization of the Cauchy--Schwarz step in section 10.2 of
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`.
The exponent parameter is `z = ρ - 1/2`; no assumption about zeta zeros
is needed for the analytic estimate itself.

-/

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.RemoteLaplaceTail

/-- The ordinary complex Laplace kernel, using the centered spectral parameter. -/
noncomputable def kernel (z : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-z * (y : ℂ))

/-- Ordinary Lebesgue L² energy, without an exponentially weighted measure. -/
noncomputable def energy (τ : ℝ → ℂ) : ℝ := ∫ y, ‖τ y‖ ^ 2

/-- Laplace transform of the portion of a function strictly after `Y`.
Changing a value at `Y` does not change this transform. -/
noncomputable def remoteTransform (τ : ℝ → ℂ) (z : ℂ) (Y : ℝ) : ℂ :=
  ∫ y in Ioi Y, τ y * kernel z y

theorem kernel_norm_sq (z : ℂ) (y : ℝ) :
    ‖kernel z y‖ ^ 2 = Real.exp (-(2 * z.re) * y) := by
  simp only [kernel, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Exact, evaluated square norm of the exponential kernel on the remote half-line. -/
theorem integral_kernel_norm_sq (z : ℂ) (hz : 0 < z.re) (Y : ℝ) :
    (∫ y in Ioi Y, ‖kernel z y‖ ^ 2) =
      Real.exp (-(2 * z.re) * Y) / (2 * z.re) := by
  simp_rw [kernel_norm_sq]
  rw [integral_exp_mul_Ioi (show -(2 * z.re) < 0 by linarith)]
  simp only [neg_div_neg_eq]

theorem kernel_memLp (z : ℂ) (hz : 0 < z.re) (Y : ℝ) :
    MemLp (kernel z) 2 (volume.restrict (Ioi Y)) := by
  have hcont : Continuous (kernel z) := by
    unfold kernel
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2
  simp_rw [kernel_norm_sq]
  exact integrableOn_exp_mul_Ioi (show -(2 * z.re) < 0 by linarith) Y

/-- Cauchy--Schwarz for the actual complex Bochner integral. -/
theorem norm_integral_mul_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ y, f y * g y ∂μ‖ ^ 2 ≤
      (∫ y, ‖f y‖ ^ 2 ∂μ) * (∫ y, ‖g y‖ ^ 2 ∂μ) := by
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) μ by simpa using hf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) μ by simpa using hg)
  have hholder' : (∫ y, ‖f y‖ * ‖g y‖ ∂μ) ≤
      Real.sqrt (∫ y, ‖f y‖ ^ 2 ∂μ) * Real.sqrt (∫ y, ‖g y‖ ^ 2 ∂μ) := by
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using hholder
  have hnorm := norm_integral_le_integral_norm (fun y => f y * g y) (μ := μ)
  simp only [norm_mul] at hnorm
  have hbound := hnorm.trans hholder'
  calc
    ‖∫ y, f y * g y ∂μ‖ ^ 2 ≤
        (Real.sqrt (∫ y, ‖f y‖ ^ 2 ∂μ) *
          Real.sqrt (∫ y, ‖g y‖ ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = (∫ y, ‖f y‖ ^ 2 ∂μ) * (∫ y, ‖g y‖ ^ 2 ∂μ) := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun y => sq_nonneg _)),
        Real.sq_sqrt (integral_nonneg (fun y => sq_nonneg _))]

/-- Exact decay coefficient in the squared remote-transform estimate. -/
theorem remoteTransform_sq_le (τ : ℝ → ℂ) (z : ℂ) (hz : 0 < z.re)
    (Y : ℝ) (hτ : MemLp τ 2 (volume.restrict (Ioi Y))) :
    ‖remoteTransform τ z Y‖ ^ 2 ≤
      (∫ y in Ioi Y, ‖τ y‖ ^ 2) *
        (Real.exp (-(2 * z.re) * Y) / (2 * z.re)) := by
  have hcs := norm_integral_mul_sq_le hτ (kernel_memLp z hz Y)
  rw [integral_kernel_norm_sq z hz Y] at hcs
  exact hcs

/-- A nonzero remote Laplace signature has an exponentially growing L² cost. -/
theorem remote_energy_lower_bound (τ : ℝ → ℂ) (z : ℂ) (hz : 0 < z.re)
    (Y : ℝ) (hτ : MemLp τ 2 (volume.restrict (Ioi Y))) :
    (2 * z.re) * Real.exp ((2 * z.re) * Y) * ‖remoteTransform τ z Y‖ ^ 2 ≤
      ∫ y in Ioi Y, ‖τ y‖ ^ 2 := by
  have hcs := remoteTransform_sq_le τ z hz Y hτ
  have hpos : 0 ≤ (2 * z.re) * Real.exp ((2 * z.re) * Y) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcs hpos
  calc
    (2 * z.re) * Real.exp ((2 * z.re) * Y) * ‖remoteTransform τ z Y‖ ^ 2 ≤
        ((2 * z.re) * Real.exp ((2 * z.re) * Y)) *
          ((∫ y in Ioi Y, ‖τ y‖ ^ 2) *
            (Real.exp (-(2 * z.re) * Y) / (2 * z.re))) := hmul
    _ = ∫ y in Ioi Y, ‖τ y‖ ^ 2 := by
      rw [show -(2 * z.re) * Y = -((2 * z.re) * Y) by ring, Real.exp_neg]
      field_simp [ne_of_gt hz, Real.exp_ne_zero]

/-- The same lower bound against the complete ordinary L² energy. -/
theorem energy_lower_bound (τ : ℝ → ℂ) (z : ℂ) (hz : 0 < z.re)
    (Y : ℝ) (hτ : MemLp τ 2 volume) :
    (2 * z.re) * Real.exp ((2 * z.re) * Y) * ‖remoteTransform τ z Y‖ ^ 2 ≤
      energy τ := by
  apply (remote_energy_lower_bound τ z hz Y (hτ.restrict (Ioi Y))).trans
  exact integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun y => sq_nonneg ‖τ y‖)) hτ.norm.integrable_sq

/-- A specified complex transform value, with every exponential constant evaluated. -/
theorem signature_energy_lower_bound (τ : ℝ → ℂ) (z : ℂ) (hz : 0 < z.re)
    (Y : ℝ) (hτ : MemLp τ 2 volume) (A : ℂ)
    (hsig : remoteTransform τ z Y = -A) :
    (2 * z.re) * Real.exp ((2 * z.re) * Y) * ‖A‖ ^ 2 ≤ energy τ := by
  have h := energy_lower_bound τ z hz Y hτ
  simpa only [hsig, norm_neg] using h

/-- The coefficient from the report, using `z = ρ - 1/2`.
The signature equation is the separate arithmetic/transform obligation. -/
theorem centered_signature_energy_lower_bound (τ : ℝ → ℂ) (ρ : ℂ)
    (hρ : 1 / 2 < ρ.re) (Y : ℝ) (hτ : MemLp τ 2 volume) (A : ℂ)
    (hsig : remoteTransform τ (ρ - 1 / 2) Y = -A) :
    (2 * ρ.re - 1) * Real.exp ((2 * ρ.re - 1) * Y) * ‖A‖ ^ 2 ≤ energy τ := by
  have hre : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by norm_num [Complex.sub_re]
  have hz : 0 < (ρ - 1 / 2).re := by
    rw [hre]
    linarith
  have hc : 2 * (ρ - 1 / 2).re = 2 * ρ.re - 1 := by
    rw [hre]
    ring
  simpa only [hc] using signature_energy_lower_bound τ (ρ - 1 / 2) hz Y hτ A hsig

/-- Exact support bridge. Only values strictly below `Y` must vanish. -/
theorem remoteTransform_eq_full_of_supported (τ : ℝ → ℂ) (z : ℂ) (Y : ℝ)
    (hsupp : ∀ y < Y, τ y = 0) :
    remoteTransform τ z Y = ∫ y, τ y * kernel z y := by
  unfold remoteTransform
  rw [← integral_Ici_eq_integral_Ioi]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hy' : y < Y := lt_of_not_ge hy
  rw [hsupp y hy', zero_mul]

/-- The actual full-transform version for a tail supported in `[Y,∞)`. -/
theorem supported_signature_energy_lower_bound (τ : ℝ → ℂ) (ρ : ℂ)
    (hρ : 1 / 2 < ρ.re) (Y : ℝ) (hτ : MemLp τ 2 volume)
    (hsupp : ∀ y < Y, τ y = 0) (A : ℂ)
    (hsig : (∫ y, τ y * kernel (ρ - 1 / 2) y) = -A) :
    (2 * ρ.re - 1) * Real.exp ((2 * ρ.re - 1) * Y) * ‖A‖ ^ 2 ≤ energy τ := by
  apply centered_signature_energy_lower_bound τ ρ hρ Y hτ A
  rw [remoteTransform_eq_full_of_supported τ (ρ - 1 / 2) Y hsupp]
  exact hsig

/-- Transform-null completions force the report's exact lower bound on tail energy.
The regularity hypotheses concern actual Bochner integrals. The vanishing
transform is a separate arithmetic input, explicitly displayed. -/
theorem null_completion_energy_lower_bound (f τ : ℝ → ℂ) (ρ : ℂ)
    (hρ : 1 / 2 < ρ.re) (Y : ℝ) (hτ : MemLp τ 2 volume)
    (hsupp : ∀ y < Y, τ y = 0)
    (hfint : Integrable (fun y => f y * kernel (ρ - 1 / 2) y))
    (hτint : Integrable (fun y => τ y * kernel (ρ - 1 / 2) y))
    (hnull : (∫ y, (f y + τ y) * kernel (ρ - 1 / 2) y) = 0) :
    (2 * ρ.re - 1) * Real.exp ((2 * ρ.re - 1) * Y) *
      ‖∫ y, f y * kernel (ρ - 1 / 2) y‖ ^ 2 ≤ energy τ := by
  apply supported_signature_energy_lower_bound τ ρ hρ Y hτ hsupp
  simp_rw [add_mul] at hnull
  rw [integral_add hfint hτint] at hnull
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hnull

end MeasureTheory.RemoteLaplaceTail
