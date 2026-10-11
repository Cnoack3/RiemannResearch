/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusSublinearEnergy
import RiemannResearch.RH.ParetoSublinearResidualTail
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import RiemannResearch.NumberTheory.MobiusReciprocalSum

/-!
# Reciprocal Möbius convergence supplies ordinary cancellation

The exact finite summation-by-parts identity is
`M(N) = N * m(N) - ∑ k < N, m(k)`, where `m(0) = 0`.
The scalar identity and Cesàro convergence proof are in
`NumberTheory/MobiusReciprocalSum`; they supply the ordinary cancellation premise
from convergence of the reciprocal sums. In particular, the canonical
sublinear-energy theorem needs only the one arithmetic provider `m(N) → 0`.
That provider is retained as an explicit hypothesis; no PNT theorem is asserted.

Source: the user-provided direct Pareto approximation manuscript, Section 3,
for the two arithmetic inputs being compared. The reduction uses elementary
finite summation by parts and Mathlib's Cesàro convergence theorem.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- The canonical full-energy result needs only reciprocal Möbius cancellation;
the ordinary cancellation premise follows by the exact Cesàro identity. -/
theorem canonicalMobiusHilbert_sublinear_of_reciprocal_cancellation
    (hm : Tendsto mobiusReciprocalSum atTop (𝓝 0)) :
    Tendsto (fun N => ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))
      atTop (𝓝 0) :=
  canonicalMobiusHilbert_sublinear_of_mobius_cancellation
    (mobius_sum_div_tendsto_zero_of_reciprocal_tendsto hm) hm

namespace CoefficientStabilization

/-- Conditional research reduction with just one arithmetic provider. The
bounded cofinal normalized residual-tail estimate is still open. -/
theorem riemannHypothesis_of_reciprocal_cancellation_and_bounded_tail
    (hm : Tendsto mobiusReciprocalSum atTop (𝓝 0))
    (C : ℝ) (hbounded : ∃ᶠ N : ℕ in atTop, (N : ℝ) * residualTailEnergy N ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_mobius_cancellation_and_bounded_tail
    (mobius_sum_div_tendsto_zero_of_reciprocal_tendsto hm) hm C hbounded

end CoefficientStabilization
end RiemannResearch.RH.Pareto
