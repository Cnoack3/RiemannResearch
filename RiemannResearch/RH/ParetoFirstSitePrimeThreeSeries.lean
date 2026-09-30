/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.NonnegativeSeriesTruncation
import RiemannResearch.RH.ParetoFirstSitePrimeAngular

/-!
# Three-series truncation of the exact prime angular energy

The full signed factorial/CRT determinant remains inside
`primeAngularInnovation`. Its summability is equivalent to the two nontrivial
deterministic conditions for an auxiliary independent symmetric-sign series.
No independence of the arithmetic rows is assumed or proved.

The probability interpretation uses Kolmogorov's three-series theorem; see
the terminology source in Analysis/NonnegativeSeriesTruncation. Only the
deterministic criteria and their existing RH consequences are formalized.
The actual clipped-energy unboundedness remains an explicit Open provider.
-/

noncomputable section
open Filter
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

open RiemannResearch.Analysis.NonnegativeEnergy

/-- Deterministic part of the three-series criterion; arithmetic independence
and the probability-space construction are not assertions of this theorem. -/
theorem primeAngularInnovation_summable_iff_three_series :
    Summable primeAngularInnovation ↔
      Summable (largeTermIndicator primeAngularInnovation 1) ∧
        Summable (truncatedEnergy primeAngularInnovation 1) :=
  summable_iff_tail_indicator_and_truncated_energy
    primeAngularInnovation primeAngularInnovation_nonneg 1 (by norm_num)

/-- Exact clipped reformulation of the angular nonsummability provider. -/
theorem primeAngularInnovation_not_summable_iff_clipped_unbounded :
    ¬ Summable primeAngularInnovation ↔
      ∀ B : ℝ, ∃ N : ℕ,
        B < ∑ n ∈ Finset.range N, min (primeAngularInnovation n) 1 :=
  not_summable_iff_clipped_prefix_unbounded
    primeAngularInnovation primeAngularInnovation_nonneg 1 (by norm_num)

/-- CONDITIONAL RESEARCH REDUCTION. The full clipped arithmetic energy
is not known to be unbounded. -/
theorem riemannHypothesis_of_clipped_prime_angular_unbounded
    (h : ∀ B : ℝ, ∃ N : ℕ,
      B < ∑ n ∈ Finset.range N, min (primeAngularInnovation n) 1) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeAngularInnovation_not_summable
    (primeAngularInnovation_not_summable_iff_clipped_unbounded.mpr h)

/-- Complete channel alternative, retaining the mean and every nonprime gain. -/
theorem tailCapacity_tendsto_iff_prime_clipped_angular_channels :
    Tendsto tailCapacity atTop atTop ↔
      (¬ Tendsto primeMeanMismatchBudget atTop (nhds 0)) ∨
        (∀ B : ℝ, ∃ N : ℕ,
          B < ∑ n ∈ Finset.range N, min (primeAngularInnovation n) 1) ∨
        (¬ Summable factorialCompositeGain) := by
  rw [tailCapacity_tendsto_iff_prime_angular_channels,
    primeAngularInnovation_not_summable_iff_clipped_unbounded]

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
