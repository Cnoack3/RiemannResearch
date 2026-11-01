import RiemannResearch.Probability.QConditionalIIDModel
import RiemannResearch.Probability.ConditionalIIDStrongLaw

/-!
# Conditional sampling limits after the exact P-to-Q change of measure

Source: user's 1 November 2026 continuation. The positive bounded density
preserves the entire probability-one event of the original common-path model,
including simultaneous Cesàro limits and recovery of the latent endpoint.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Probability.QConditionalIID
open ConditionalIID

/-- One probability-one event works for every real arithmetic observable under Q.
No global moment hypothesis is required, since every conditional fiber is finite. -/
theorem observationAverage_strongLaw_simultaneous :
    ∀ᵐ ω ∂probability, ∀ F : ℕ → ℝ,
      Tendsto (fun r => pathAverage F r ω.2) atTop (𝓝 (cesaro F (endpoint ω))) :=
  (probability_ae_iff _).mpr ConditionalIID.observationAverage_strongLaw_simultaneous

/-- The same row observations recover the endpoint under either common-space law. -/
theorem runningMaximum_eventually_eq_endpoint :
    ∀ᵐ ω ∂probability, ∀ᶠ r in atTop, runningMaximum r ω = endpoint ω :=
  (probability_ae_iff _).mpr ConditionalIID.runningMaximum_eventually_eq_endpoint

end RiemannResearch.Probability.QConditionalIID
