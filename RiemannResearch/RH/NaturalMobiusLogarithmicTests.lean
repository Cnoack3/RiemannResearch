/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.DivisorCountLogSummability
import RiemannResearch.RH.NaturalMobiusResidualCriterion

/-!
# Logarithmic physical-primitive tests for the raw Mobius residual

Source: the Abel-pairing mechanism in `NaturalMobiusPrimitiveTests` and the
unconditional Dirichlet-convolution majorant in `DivisorCountLogSummability`.
This specializes the established summable-primitive theorem to the bound
 |H_f(K)| <= C (K+1) / log(2(K+1))^p, p > 2,
where H_f is the partial sum of the positive physical coordinates of f.
These physical partial sums are not the weighted signed Pareto tails.

The pairing limit uses the already proved PNT source. No RH is assumed.
The displayed bound for a specified f is an explicit hypothesis; this module
provides no such bound for the actual limiting residual and therefore proves
no unconditional RH statement. The final RH implication keeps that physical
primitive estimate as an explicit, unproved hypothesis.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.RH.Pareto

/-- Critical logarithmic improvement of the primitive test class. -/
theorem rawMobiusResidual_inner_tendsto_of_primitive_log_bound
    (f : ThresholdHilbert) (C p : ℝ) (hp : 2 < p)
    (hH : ∀ K : ℕ, |∑ k ∈ Finset.range K, hilbertSequence f (k + 1)| ≤
      C * (((K : ℝ) + 1) / Real.log (2 * ((K : ℝ) + 1)) ^ p)) :
    Tendsto (fun N => inner ℝ (hilbertOne - rawMobiusHilbert N) f)
      atTop (𝓝 0) := by
  apply rawMobiusResidual_inner_tendsto_of_summable_primitive f
  have hs :=
    (RiemannResearch.NumberTheory.summable_logarithmic_divisor_count_successor_majorant
      hp).mul_left C
  apply hs.of_nonneg_of_le
  · intro K
    positivity
  · intro K
    calc
      _ ≤ (C * (((K : ℝ) + 1) / Real.log (2 * ((K : ℝ) + 1)) ^ p)) *
          ((3 + ((K + 1).divisors.card : ℝ)) /
            (((K : ℝ) + 1) * ((K : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_right (hH K) (by positivity)
      _ = _ := by ring

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Conditional research result: the physical primitive bound for the actual
limiting residual is the unproved input. -/
theorem riemannHypothesis_of_residual_primitive_log_bound
    (C p : ℝ) (hp : 2 < p)
    (hH : ∀ K : ℕ, |∑ k ∈ Finset.range K,
      hilbertSequence limitResidual (k + 1)| ≤
        C * (((K : ℝ) + 1) / Real.log (2 * ((K : ℝ) + 1)) ^ p)) :
    RiemannHypothesis := by
  have ht := rawMobiusResidual_inner_tendsto_of_primitive_log_bound
    limitResidual C p hp hH
  have hc : Tendsto (fun _ : ℕ => limitEnergy) atTop (𝓝 0) := by
    simpa only [rawMobiusResidual_inner_limitResidual] using ht
  have he : limitEnergy = 0 := tendsto_nhds_unique tendsto_const_nhds hc
  apply riemannHypothesis_of_firstCoordinate_zero
  exact firstCoordinate_zero_iff_residual_zero.mpr
    (limitResidual_zero_iff_energy_zero.mpr he)

end RiemannResearch.RH.Pareto.CoefficientStabilization
