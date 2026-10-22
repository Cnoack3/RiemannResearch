import RiemannResearch.Analysis.SmoothCorrelationClosure
import RiemannResearch.RH.SignedWeilCorrelation

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Full admissibility of the actual real autocorrelation

All derivatives and their exponential bounds are supplied by the actual
correlation and real-projection closure theorems.
-/

open RiemannResearch.Analysis

namespace RiemannResearch.RH.SignedWeilCorrelation

theorem smoothSuperexponentialDecay_realAutocorrelation {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) :
    SmoothSuperexponentialDecay (fun t => (realAutocorrelation f t : ℂ)) :=
  (hf.crossCorrelation hf).realPartEmbedding

end RiemannResearch.RH.SignedWeilCorrelation
