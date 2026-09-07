import RiemannResearch.Analysis.SuperexponentialLaplace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Linear

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual differential operator under the bilateral Laplace integral

Integration by parts is proved using integrability of both the weighted function
and its derivative. Mathlib then proves that the boundary values at both ends
are zero. No boundary cancellation or transform identity is assumed.
-/

open MeasureTheory

namespace MeasureTheory.BilateralLaplace

theorem hasDerivAt_kernel_spatial (s : ℂ) (y : ℝ) :
    HasDerivAt (kernel s) (-s * kernel s y) y := by
  have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) y := by
    convert (Complex.ofRealCLM.hasDerivAt (x := y)) using 1 <;> rfl
  have hlin : HasDerivAt (fun x : ℝ => -s * (x : ℂ)) (-s) y := by
    simpa using hid.const_mul (-s)
  change HasDerivAt (fun x : ℝ => Complex.exp (-s * (x : ℂ)))
    (-s * Complex.exp (-s * (y : ℂ))) y
  convert hlin.cexp using 1 <;> first | rfl | ring

/-- The boundary terms vanish as a consequence of actual absolute integrability. -/
theorem transform_of_hasDerivAt {f f' : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hf' : HasExponentialMoments f')
    (hd : ∀ y : ℝ, HasDerivAt f (f' y) y) (s : ℂ) :
    transform f' s = s * transform f s := by
  have hi := integrable_integrand hf s
  have hi' := integrable_integrand hf' s
  have hD : ∀ y : ℝ, HasDerivAt (fun x : ℝ => f x * kernel s x)
      (f' y * kernel s y - s * (f y * kernel s y)) y := by
    intro y
    have hmul := (hd y).mul (hasDerivAt_kernel_spatial s y)
    convert hmul using 1 <;> first | rfl | ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hD
    (hi'.sub (hi.const_mul s)) hi
  rw [integral_sub hi' (hi.const_mul s), integral_const_mul] at hz
  exact sub_eq_zero.mp hz

theorem centeredTransform_of_hasDerivAt {f f' : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hf' : HasExponentialMoments f')
    (hd : ∀ y : ℝ, HasDerivAt f (f' y) y) (s : ℂ) :
    centeredTransform f' s = (s - 1 / 2) * centeredTransform f s :=
  transform_of_hasDerivAt hf hf' hd (s - 1 / 2)

theorem centeredTransform_deriv {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hf' : HasExponentialMoments (deriv f))
    (hd : Differentiable ℝ f) (s : ℂ) :
    centeredTransform (deriv f) s = (s - 1 / 2) * centeredTransform f s :=
  centeredTransform_of_hasDerivAt hf hf' (fun y => (hd y).hasDerivAt) s

theorem centeredTransform_second_deriv {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hf' : HasExponentialMoments (deriv f))
    (hf'' : HasExponentialMoments (deriv (deriv f)))
    (hd : Differentiable ℝ f) (hd' : Differentiable ℝ (deriv f)) (s : ℂ) :
    centeredTransform (deriv (deriv f)) s =
      (s - 1 / 2) ^ 2 * centeredTransform f s := by
  rw [centeredTransform_deriv hf' hf'' hd' s,
    centeredTransform_deriv hf hf' hd s]
  ring


end MeasureTheory.BilateralLaplace

namespace RiemannResearch.Analysis

theorem SuperexponentialDecay.centeredTransform_deriv {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hf' : SuperexponentialDecay (deriv f))
    (hd : Differentiable ℝ f) (hc' : Continuous (deriv f)) (s : ℂ) :
    BilateralLaplace.centeredTransform (deriv f) s =
      (s - 1 / 2) * BilateralLaplace.centeredTransform f s :=
  BilateralLaplace.centeredTransform_deriv
    (hf.hasExponentialMoments hd.continuous) (hf'.hasExponentialMoments hc') hd s


end RiemannResearch.Analysis
