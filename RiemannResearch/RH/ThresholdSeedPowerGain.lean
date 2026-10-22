import RiemannResearch.RH.ThresholdSeedPowerInfinite5040
import RiemannResearch.RH.ThresholdConductor2520DualLower
import RiemannResearch.RH.OneBoundaryRepairObstruction
import Mathlib.Tactic.Linarith

/-!
# Uniform full-error improvement by raising the seed-2 exponent

Source: exact rational primal and dual certificates constructed in this research
continuation. The comparison is against every real coefficient choice in the
entire conductor-2520 span and uses the complete infinite error.
-/

namespace RiemannResearch.RH.TwoSeedThreshold
open Pareto

/-- The new witness beats every conductor-2520 combination by more than 0.0029. -/
theorem legalWitness5040_uniform_improvement (c : Fin 68 → ℝ) :
    (∑' k : ℕ, positiveWeight (k + 1) * (1 - legalWitness5040 (k + 1)) ^ 2) +
      (29 : ℝ) / 10000 <
        ∑' k : ℕ, positiveWeight (k + 1) *
          (1 - conductor2520Combination c (k + 1)) ^ 2 := by
  linarith [legalWitness5040_full_error_lt, conductor2520Combination_full_error_gt c]

/-- The explicit witness beats the entire balanced one-boundary repair class. -/
theorem legalWitness5040_beats_single_boundary_repairs {ι : Type*}
    (K A B : ℕ) (s : Finset ι) (N : ι → ℕ) (q : ι → ℝ)
    (hK : 6 ≤ K) (hT : K < 2 ^ A * 3 ^ B)
    (hN : ∀ i ∈ s, 0 < N i)
    (hother : ∀ i ∈ s, ¬ N i ∣ 2 ^ A * 3 ^ B)
    (hbalance : OneBoundaryRepair.headRepairBalance K s N q) :
    (∑' k : ℕ, PositiveSeedCone.weightedError legalWitness5040 k) +
      (149 : ℝ) / 9000 <
        ∑' k : ℕ, PositiveSeedCone.weightedError
          (OneBoundaryRepair.repairedHead K (2 ^ A * 3 ^ B) s N q) k := by
  have hu : (∑' k : ℕ, PositiveSeedCone.weightedError legalWitness5040 k) <
      (39 : ℝ) / 1000 := legalWitness5040_full_error_lt
  have hl := OneBoundaryRepair.smooth_single_boundary_fullError_lower
    K A B s N q hK hT hN hother hbalance
  linarith

end RiemannResearch.RH.TwoSeedThreshold
