import RiemannResearch.RH.ThresholdPrimeSevenInfinite2520
import RiemannResearch.RH.ThresholdConductor360DualLower
import RiemannResearch.RH.BoundedSeedConductorObstruction
import Mathlib.Tactic.Linarith

/-!
# Uniform improvement from the prime-seven enlargement

The signed rational witness is compared against every real coefficient choice
in the full conductor-360 generator list. Both full infinite-error bounds are
proved by the imported certificates; there is no numerical optimality premise.
-/
namespace RiemannResearch.RH.TwoSeedThreshold
open Pareto

/-- The conductor-2520 witness beats every conductor-360 combination by more than .0011. -/
theorem legalWitness2520_uniform_improvement (c : Fin 34 → ℝ) :
    (∑' k : ℕ, positiveWeight (k + 1) * (1 - legalWitness2520 (k + 1)) ^ 2) +
      (11 : ℝ) / 10000 <
        ∑' k : ℕ, positiveWeight (k + 1) *
          (1 - conductor360Combination c (k + 1)) ^ 2 := by
  linarith [legalWitness2520_full_error_lt, conductor360Combination_full_error_gt c]

/-- Keeping the current powers of both seeds cannot halve the new witness's error. -/
theorem legalWitness2520_error_half_lt_of_boundedSeedCaps {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M)
    (h16 : ¬ 16 ∣ M) (h27 : ¬ 27 ∣ M) :
    (∑' k : ℕ, PositiveSeedCone.weightedError legalWitness2520 k) / 2 <
      ∑' k : ℕ, PositiveSeedCone.weightedError
        (PositiveSeedCone.seedCombination s a m c) k := by
  have hu : (∑' k : ℕ, PositiveSeedCone.weightedError legalWitness2520 k) <
      (421 : ℝ) / 10000 := legalWitness2520_full_error_lt
  have hl := BoundedSeedConductorObstruction.conductor_seedCaps_three_two_fullError_lower
    s a m c M ha hm hperiod h16 h27
  linarith

end RiemannResearch.RH.TwoSeedThreshold
