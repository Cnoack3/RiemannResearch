import RiemannResearch.Analysis.SuperexponentialDecay
import RiemannResearch.Analysis.BilateralLaplaceEntire

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Superexponential decay implies an entire actual bilateral transform

This combines the pointwise decay-to-integrability theorem with differentiation
under the actual Bochner integral. No holomorphy or transform identity is assumed.
-/

open MeasureTheory

namespace RiemannResearch.Analysis

theorem SuperexponentialDecay.hasExponentialMoments {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hcont : Continuous f) :
    BilateralLaplace.HasExponentialMoments f :=
  BilateralLaplace.hasExponentialMoments_of_weighted_integrable
    hcont.aestronglyMeasurable
    (fun _ ha => hf.integrable_weighted_norm hcont (le_of_lt ha))

theorem SuperexponentialDecay.differentiable_centeredTransform {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hcont : Continuous f) :
    Differentiable ℂ (BilateralLaplace.centeredTransform f) :=
  BilateralLaplace.differentiable_centeredTransform (hf.hasExponentialMoments hcont)

theorem SuperexponentialDecay.analyticAt_centeredTransform {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hcont : Continuous f) (s : ℂ) :
    AnalyticAt ℂ (BilateralLaplace.centeredTransform f) s :=
  BilateralLaplace.analyticAt_centeredTransform (hf.hasExponentialMoments hcont) s

theorem SuperexponentialDecay.centeredTransform_eq_of_rightHalfPlane
    {f : ℝ → ℂ} {G : ℂ → ℂ}
    (hf : SuperexponentialDecay f) (hcont : Continuous f)
    (hG : Differentiable ℂ G)
    (hmatch : ∀ s : ℂ, 1 < s.re → BilateralLaplace.centeredTransform f s = G s) :
    BilateralLaplace.centeredTransform f = G :=
  BilateralLaplace.centeredTransform_eq_of_rightHalfPlane
    (hf.hasExponentialMoments hcont) hG hmatch

end RiemannResearch.Analysis
