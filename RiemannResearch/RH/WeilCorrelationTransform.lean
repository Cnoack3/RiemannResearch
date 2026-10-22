import RiemannResearch.Analysis.BilateralLaplaceRealPart
import RiemannResearch.Analysis.CrossCorrelationRegularity
import RiemannResearch.RH.SignedWeilCorrelation

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Spectral nullity of the actual real autocorrelation

The correlation is the concrete Bochner integral from the arithmetic Weil
functional. Its transform vanishing follows by Fubini and real projection;
no spectral-correlation identity is an input.
-/

open MeasureTheory
open RiemannResearch.Analysis

namespace RiemannResearch.RH.SignedWeilCorrelation

theorem realAutocorrelation_transform_zero {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hdf : SuperexponentialDecay (deriv f))
    (hfd : Differentiable ℝ f) (s : ℂ)
    (hs : BilateralLaplace.centeredTransform f s = 0)
    (hreflect : BilateralLaplace.centeredTransform f (1 - s) = 0) :
    BilateralLaplace.transform (fun t => (realAutocorrelation f t : ℂ))
      (s - 1 / 2) = 0 := by
  have hfc := hfd.continuous
  obtain ⟨K, hK⟩ := hf.exists_crossCorrelation_lipschitz hf hdf hfd hfc
  have hCc : Continuous (RiemannResearch.Analysis.crossCorrelation f f) := hK.continuous
  have hCm := (hf.crossCorrelation hf hfc hfc).hasExponentialMoments hCc
  have hneg : BilateralLaplace.transform f (-(s - 1 / 2)) = 0 := by
    change BilateralLaplace.transform f ((1 - s) - 1 / 2) = 0 at hreflect
    rwa [show (1 - s) - 1 / 2 = -(s - 1 / 2) by ring] at hreflect
  change BilateralLaplace.transform
    (fun t => ((RiemannResearch.Analysis.crossCorrelation f f t).re : ℂ))
      (s - 1 / 2) = 0
  exact BilateralLaplace.transform_realPart_crossCorrelation_zero
    (hf.hasExponentialMoments hfc) hfc hCm hCc (s - 1 / 2) hs hneg

end RiemannResearch.RH.SignedWeilCorrelation
