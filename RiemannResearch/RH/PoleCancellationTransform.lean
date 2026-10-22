import RiemannResearch.Analysis.BilateralLaplaceDifferential
import RiemannResearch.RH.ArithmeticCompletionDifferential

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Exact Laplace transform of the concrete pole-cancellation operator

Combines real integration by parts with the actual RH operator D²−1/4.
The Analysis modules retain no dependency on the RH theorem library.
-/

open MeasureTheory

namespace MeasureTheory.BilateralLaplace

theorem centeredTransform_poleCancellationOperator {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hf' : HasExponentialMoments (deriv f))
    (hf'' : HasExponentialMoments (deriv (deriv f)))
    (hd : Differentiable ℝ f) (hd' : Differentiable ℝ (deriv f)) (s : ℂ) :
    centeredTransform (RiemannResearch.RH.poleCancellationOperator f) s =
      s * (s - 1) * centeredTransform f s := by
  have hi := integrable_integrand hf (s - 1 / 2)
  have hi'' := integrable_integrand hf'' (s - 1 / 2)
  have hsplit :
      centeredTransform (RiemannResearch.RH.poleCancellationOperator f) s =
        centeredTransform (deriv (deriv f)) s -
          (1 / 4 : ℂ) * centeredTransform f s := by
    simp only [centeredTransform, transform, RiemannResearch.RH.poleCancellationOperator,
      Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      sub_mul, mul_assoc]
    rw [integral_sub hi'' (hi.const_mul (1 / 4 : ℂ)), integral_const_mul]
  rw [hsplit, centeredTransform_second_deriv hf hf' hf'' hd hd' s]
  ring


end MeasureTheory.BilateralLaplace

namespace RiemannResearch.Analysis

theorem SuperexponentialDecay.centeredTransform_poleCancellationOperator {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hf' : SuperexponentialDecay (deriv f))
    (hf'' : SuperexponentialDecay (deriv (deriv f)))
    (hd : Differentiable ℝ f) (hd' : Differentiable ℝ (deriv f))
    (hc'' : Continuous (deriv (deriv f))) (s : ℂ) :
    BilateralLaplace.centeredTransform (RiemannResearch.RH.poleCancellationOperator f) s =
      s * (s - 1) * BilateralLaplace.centeredTransform f s :=
  BilateralLaplace.centeredTransform_poleCancellationOperator
    (hf.hasExponentialMoments hd.continuous)
    (hf'.hasExponentialMoments hd'.continuous)
    (hf''.hasExponentialMoments hc'') hd hd' s


end RiemannResearch.Analysis
