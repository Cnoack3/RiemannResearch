import RiemannResearch.RH.ResidueTailAdditiveCancellation
import RiemannResearch.RH.ParetoTailCapacityDuality

/-!
# Canonical signed-tail regularity and the RH endpoint

Source: user-provided continuation, Sections 26 and 31, for the regularity
condition and intended contradiction. The provider remains explicitly Open.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

/-- Open arithmetic provider from Section 31.1. This is a proposition, not an axiom. -/
def CanonicalTailSummability : Prop :=
  pointDualResidual ≠ 0 →
    Summable (anchoredSignedTail (hilbertSequence canonicalTailCertificate))

/-- Precisely identifies the strength of the remaining regularity provider. -/
theorem canonicalTailSummability_iff_pointDualResidual_eq_zero :
    CanonicalTailSummability ↔ pointDualResidual = 0 := by
  constructor
  · intro h
    by_contra hr
    exact tailCertificate_not_summable_signedTail canonicalTailCertificate
      (canonicalTailCertificate_isCertificate hr) (h hr)
  · intro h hr
    exact (hr h).elim

/-- Conditional research reduction: the canonical primitive summability provider
is not discharged by Hilbert membership or signed-tail rigidity. -/
theorem riemannHypothesis_of_canonicalTailSummability
    (h : CanonicalTailSummability) : RiemannHypothesis := by
  have hr := canonicalTailSummability_iff_pointDualResidual_eq_zero.mp h
  apply riemannHypothesis_of_firstPoint_error_tendsto_zero
  apply (RiemannResearch.Analysis.ExhaustiveWalk.walkError_tendsto_zero_iff
    residueAtom id Function.surjective_id (paretoPointHilbert 0)).mpr
  have heq : paretoPointHilbert 0 = closedSpace.starProjection (paretoPointHilbert 0) :=
    sub_eq_zero.mp hr
  exact heq.symm ▸ closedSpace.starProjection_apply_mem (paretoPointHilbert 0)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

/-- A concrete additive-cancellation input suffices for the canonical RH endpoint.
This theorem does not assert the input for the actual canonical certificate. -/
theorem riemannHypothesis_of_canonicalAdditiveCancellation
    (h : Summable (fun n : ℕ =>
      |additivePartialSum (hilbertSequence canonicalTailCertificate) n| / (n : ℝ)^2)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_canonicalTailSummability
  intro _
  exact anchoredSignedTail_summable_of_additiveCancellation
    (hilbertSequence canonicalTailCertificate)
    (hilbertSequence_square_summable canonicalTailCertificate)
    (summable_additiveCancellation_of_div_square (hilbertSequence canonicalTailCertificate) h)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
