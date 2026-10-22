import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal
import RiemannResearch.RH.CanonicalMobiusCesaro

/-!
# Canonical Möbius energy from the prime number theorem

The scalar reciprocal-sum limit is proved in
`NumberTheory/PrimeNumberTheorem/MobiusReciprocal`; the exact finite summation
identities are in `NumberTheory/MobiusReciprocalSum`. This module assembles that
unconditional scalar result with the canonical Pareto energy reduction.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- Classical Möbius cancellation discharges the canonical sublinear
full-energy premise. This does not assert bounded or vanishing full energy. -/
theorem canonicalMobiusHilbert_sublinear :
    Tendsto (fun N => ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))
      atTop (𝓝 0) :=
  canonicalMobiusHilbert_sublinear_of_reciprocal_cancellation
    mobiusReciprocalSum_tendsto_zero

end RiemannResearch.RH.Pareto
