import RiemannResearch.RH.ThresholdPrimeFiveInfinite180
import RiemannResearch.RH.ThresholdPrimeFiveInfinite360
import RiemannResearch.RH.ThresholdConductor36DualLower
import Mathlib.Tactic.Linarith

/-! Strict uniform improvement from the certified prime-five dilation witnesses. -/
namespace RiemannResearch.RH.TwoSeedThreshold
open Pareto

/-- The conductor-180 witness beats every conductor-36 combination by more than .002. -/
theorem legalWitness180_uniform_improvement (c : Fin 12 → ℝ) :
    (∑' k : ℕ, positiveWeight (k+1) * (1-legalWitness180 (k+1))^2) +
      (2 : ℝ)/1000 <
        ∑' k : ℕ, positiveWeight (k+1) * (1-conductor36Combination c (k+1))^2 := by
  linarith [legalWitness180_full_error_lt, conductor36Combination_full_error_gt c]

/-- The conductor-360 witness beats every conductor-36 combination by more than .005. -/
theorem legalWitness360_uniform_improvement (c : Fin 12 → ℝ) :
    (∑' k : ℕ, positiveWeight (k+1) * (1-legalWitness360 (k+1))^2) +
      (5 : ℝ)/1000 <
        ∑' k : ℕ, positiveWeight (k+1) * (1-conductor36Combination c (k+1))^2 := by
  linarith [legalWitness360_full_error_lt, conductor36Combination_full_error_gt c]

end RiemannResearch.RH.TwoSeedThreshold
