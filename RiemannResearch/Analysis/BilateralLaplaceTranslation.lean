import RiemannResearch.Analysis.BilateralLaplaceEntire
import Mathlib.MeasureTheory.Group.Integral

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Translation of the actual bilateral Laplace integral

No integrability hypothesis is needed: Bochner integration and the exact
translation-invariance/scalar identities cover the nonintegrable case too.
-/

open MeasureTheory

namespace MeasureTheory.BilateralLaplace

theorem kernel_add (s : ℂ) (x t : ℝ) :
    kernel s (x + t) = kernel s x * kernel s t := by
  simp only [kernel, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem transform_const_mul (f : ℝ → ℂ) (c s : ℂ) :
    transform (fun y => c * f y) s = c * transform f s := by
  simp only [transform, mul_assoc, integral_const_mul]

theorem transform_translate (f : ℝ → ℂ) (s : ℂ) (t : ℝ) :
    transform (fun y => f (y - t)) s = kernel s t * transform f s := by
  have hshift : transform (fun y => f (y - t)) s =
      ∫ y : ℝ, f y * kernel s (y + t) := by
    simpa [transform] using
      (integral_sub_right_eq_self (fun y : ℝ => f y * kernel s (y + t)) t)
  rw [hshift]
  simp_rw [kernel_add]
  unfold transform
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem centeredTransform_const_mul (f : ℝ → ℂ) (c s : ℂ) :
    centeredTransform (fun y => c * f y) s = c * centeredTransform f s :=
  transform_const_mul f c (s - 1 / 2)

theorem centeredTransform_translate (f : ℝ → ℂ) (s : ℂ) (t : ℝ) :
    centeredTransform (fun y => f (y - t)) s =
      Complex.exp (-(s - 1 / 2) * (t : ℂ)) * centeredTransform f s :=
  transform_translate f (s - 1 / 2) t

end MeasureTheory.BilateralLaplace
