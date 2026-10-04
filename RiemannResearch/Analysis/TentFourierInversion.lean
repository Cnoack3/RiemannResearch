import RiemannResearch.Analysis.TentFourierIntegral
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absolute integrability and actual Fourier inversion for the tent

The Cauchy majorant combines the two exact bounds: total mass `v²` and
inverse-square frequency decay. There is no assumed inversion formula.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace RiemannResearch.Analysis.TentFourierInversion

open MarkedFourierTail TentFourierIntegral

theorem tentTransform_nonneg (v α : ℝ) : 0 ≤ tentTransform v α := by
  unfold tentTransform
  split <;> positivity

/-- The small-frequency bound needed for absolute integrability. -/
theorem tentTransform_le_mass (v α : ℝ) : tentTransform v α ≤ v ^ 2 := by
  by_cases hα : α = 0
  · simp [tentTransform, hα]
  · have hpa : Real.pi * α ≠ 0 := mul_ne_zero Real.pi_ne_zero hα
    have hs : Real.sin (Real.pi * v * α) ^ 2 ≤ (Real.pi * v * α) ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg _)
        (Real.abs_sin_le_abs (x := Real.pi * v * α))
      simpa only [← pow_two, sq_abs] using h
    rw [tentTransform, if_neg hα, div_pow]
    apply (div_le_iff₀ (sq_pos_of_ne_zero hpa)).2
    calc
      _ ≤ (Real.pi * v * α) ^ 2 := hs
      _ = _ := by ring

theorem tentTransform_mul_sq_le (v α : ℝ) :
    tentTransform v α * α ^ 2 ≤ 1 / Real.pi ^ 2 := by
  by_cases hα : α = 0
  · simp only [hα, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    positivity
  · calc
      _ ≤ (1 / (Real.pi ^ 2 * α ^ 2)) * α ^ 2 :=
        mul_le_mul_of_nonneg_right (tentTransform_le_inverse_square v hα) (sq_nonneg _)
      _ = _ := by field_simp [hα, Real.pi_ne_zero]

/-- A single globally integrable Cauchy majorant, with no frequency gap. -/
theorem tentTransform_le_cauchy_majorant (v α : ℝ) :
    tentTransform v α ≤ (v ^ 2 + 1 / Real.pi ^ 2) * (1 + α ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + α ^ 2)).2
  nlinarith [tentTransform_le_mass v α, tentTransform_mul_sq_le v α]

theorem tentTransform_measurable (v : ℝ) : Measurable (tentTransform v) := by
  unfold tentTransform
  apply Measurable.ite
  · simpa using (measurableSet_singleton (0 : ℝ))
  · exact measurable_const
  · fun_prop

theorem tentTransform_integrable_complex (v : ℝ) :
    Integrable (fun α : ℝ => (tentTransform v α : ℂ)) := by
  apply (integrable_inv_one_add_sq.const_mul (v ^ 2 + 1 / Real.pi ^ 2)).mono'
  · exact (Complex.measurable_ofReal.comp (tentTransform_measurable v)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro α
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tentTransform_nonneg v α)]
    exact tentTransform_le_cauchy_majorant v α

theorem fourier_tent_integrable (v : ℝ) (hv : 0 ≤ v) :
    Integrable (𝓕 (fun x : ℝ => (tent v x : ℂ))) := by
  have heq : 𝓕 (fun x : ℝ => (tent v x : ℂ)) =
      (fun α : ℝ => (tentTransform v α : ℂ)) := by
    funext α
    exact fourier_tent_eq_tentTransform v hv α
  rw [heq]
  exact tentTransform_integrable_complex v

/-- Exact inversion holds at every point, including the two support endpoints. -/
theorem fourierInv_tentTransform (v : ℝ) (hv : 0 ≤ v) (x : ℝ) :
    𝓕⁻ (fun α : ℝ => (tentTransform v α : ℂ)) x = (tent v x : ℂ) := by
  have hcont : Continuous (fun x : ℝ => (tent v x : ℂ)) := by
    unfold tent
    fun_prop
  have hint : Integrable (fun x : ℝ => (tent v x : ℂ)) := (tent_integrable v).ofReal
  have h := hcont.fourierInv_fourier_eq hint (fourier_tent_integrable v hv)
  have heq : 𝓕 (fun x : ℝ => (tent v x : ℂ)) =
      (fun α : ℝ => (tentTransform v α : ℂ)) := by
    funext α
    exact fourier_tent_eq_tentTransform v hv α
  rw [heq] at h
  exact congrFun h x

/-- The absolutely convergent ordinary integral version of tent inversion. -/
theorem integral_tentTransform_phase (v : ℝ) (hv : 0 ≤ v) (x : ℝ) :
    (∫ α : ℝ, Complex.exp (((2 * Real.pi * α * x : ℝ) : ℂ) * Complex.I) *
      (tentTransform v α : ℂ)) = (tent v x : ℂ) := by
  have h := fourierInv_tentTransform v hv x
  rw [Real.fourierInv_eq'] at h
  simpa only [RCLike.inner_apply', starRingEnd_apply, star_trivial, smul_eq_mul,
    mul_assoc] using h

end RiemannResearch.Analysis.TentFourierInversion
