import RiemannResearch.Analysis.InconsistentPenaltyLimits
import RiemannResearch.RH.RamanujanAttainableObservations
import RiemannResearch.RH.RamanujanPenaltyPath

/-!
# Actual Pareto/Q limits for arbitrary coefficient requests

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
The hard-penalty limit isolates exactly the arithmetic impossible cost.
The final total-action identity includes the full physical and coordinate
motion and applies even to inconsistent or redundant conductor requests.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanInconsistentPenaltyLimits
open Pareto ZetaTwoHilbert
open RamanujanRegularizedConstraints (constraintMatrix coordinateMismatch observe_eq)
open RamanujanCanonicalOptimizer (packetMultipleTransform)
open RamanujanAttainableObservations RamanujanPenaltyPath
open RiemannResearch.Analysis.FiniteRegularizedConstraints
open RiemannResearch.Analysis.InconsistentPenaltyLimits
variable {κ : Type*} [Fintype κ]

theorem pareto_mismatch_limit {α : Type*} {l : Filter α}
    (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (r : α → ℝ)
    (hne : ∀ᶠ i in l, r i ≠ 0)
    (hinv : Tendsto (fun i => 1 / (r i) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => coordinateMismatch n m t
      (RamanujanRegularizedConstraints.regularizedCoefficients n m t (r i))) l (𝓝 (impossibleCost n m t)) := by
  simpa only [mismatchEnergy, observe_eq, coordinateMismatch, impossibleCost,
    RamanujanRegularizedConstraints.regularizedCoefficients] using
      mismatch_tendsto_inconsistency (finitePacket_independent n) (constraintMatrix n m) hilbertOne t r hne hinv

theorem pareto_normalized_minimum_limit {α : Type*} {l : Filter α}
    (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (r : α → ℝ)
    (hne : ∀ᶠ i in l, r i ≠ 0)
    (hinv : Tendsto (fun i => 1 / (r i) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => RamanujanRegularizedConstraints.penalizedError n m t (r i)
      (RamanujanRegularizedConstraints.regularizedCoefficients n m t (r i)) / (r i) ^ 2) l
        (𝓝 (impossibleCost n m t)) := by
  simpa only [RamanujanRegularizedConstraints.objective_eq, impossibleCost,
    RamanujanRegularizedConstraints.regularizedCoefficients] using
      normalized_minimum_tendsto_inconsistency (finitePacket_independent n) (constraintMatrix n m) hilbertOne t r hne hinv

theorem pareto_zero_mismatch_iff {α : Type*} {l : Filter α} [NeBot l]
    (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (r : α → ℝ)
    (hne : ∀ᶠ i in l, r i ≠ 0)
    (hinv : Tendsto (fun i => 1 / (r i) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => coordinateMismatch n m t
      (RamanujanRegularizedConstraints.regularizedCoefficients n m t (r i))) l (𝓝 0) ↔
      ∃ a : Fin n → ℝ, ∀ j, packetMultipleTransform n a (m j) = t j := by
  simpa only [mismatchEnergy, observe_eq, coordinateMismatch,
    RamanujanRegularizedConstraints.regularizedCoefficients] using
      zero_mismatch_limit_iff (finitePacket_independent n) (constraintMatrix n m) hilbertOne t r hne hinv

theorem pareto_total_action_impossible_cost (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (r : ℕ → ℝ)
    (hstep : ∀ k, (r k) ^ 2 ≤ (r (k + 1)) ^ 2)
    (hne : ∀ᶠ k in atTop, r k ≠ 0)
    (hinv : Tendsto (fun k => 1 / (r k) ^ 2) atTop (𝓝 0)) :
    (∑' k, paretoAction n m t (r k) (r (k + 1))) =
      coordinateMismatch n m t (RamanujanRegularizedConstraints.regularizedCoefficients n m t (r 0)) -
        impossibleCost n m t :=
by
  simpa only [paretoAction, RiemannResearch.Analysis.RegularizedPathAction.penaltyAction,
    RamanujanRegularizedConstraints.regularizedCandidate, RamanujanRegularizedConstraints.regularizedCoefficients,
    map_sub, coordinateMismatch, mismatchEnergy, observe_eq, impossibleCost] using
      total_action_exact (finitePacket_independent n) (constraintMatrix n m) hilbertOne t r hstep hne hinv

theorem q_mismatch_limit {α : Type*} {l : Filter α}
    (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (r : α → ℝ)
    (hne : ∀ᶠ i in l, r i ≠ 0)
    (hinv : Tendsto (fun i => 1 / (r i) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => coordinateMismatch n m t
      (QRamanujanRegularizedConstraints.regularizedCoefficients n m t (r i))) l (𝓝 (impossibleCost n m t)) := by
  simpa only [mismatchEnergy, observe_eq, coordinateMismatch, impossibleCost,
    QRamanujanRegularizedConstraints.regularizedCoefficients] using
      mismatch_tendsto_inconsistency (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t r hne hinv

theorem q_normalized_minimum_limit {α : Type*} {l : Filter α}
    (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (r : α → ℝ)
    (hne : ∀ᶠ i in l, r i ≠ 0)
    (hinv : Tendsto (fun i => 1 / (r i) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => QRamanujanRegularizedConstraints.penalizedError n m t (r i)
      (QRamanujanRegularizedConstraints.regularizedCoefficients n m t (r i)) / (r i) ^ 2) l
        (𝓝 (impossibleCost n m t)) := by
  simpa only [QRamanujanRegularizedConstraints.objective_eq, impossibleCost,
    QRamanujanRegularizedConstraints.regularizedCoefficients] using
      normalized_minimum_tendsto_inconsistency (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t r hne hinv

theorem q_zero_mismatch_iff {α : Type*} {l : Filter α} [NeBot l]
    (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (r : α → ℝ)
    (hne : ∀ᶠ i in l, r i ≠ 0)
    (hinv : Tendsto (fun i => 1 / (r i) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => coordinateMismatch n m t
      (QRamanujanRegularizedConstraints.regularizedCoefficients n m t (r i))) l (𝓝 0) ↔
      ∃ a : Fin n → ℝ, ∀ j, packetMultipleTransform n a (m j) = t j := by
  simpa only [mismatchEnergy, observe_eq, coordinateMismatch,
    QRamanujanRegularizedConstraints.regularizedCoefficients] using
      zero_mismatch_limit_iff (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t r hne hinv

theorem q_total_action_impossible_cost (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (r : ℕ → ℝ)
    (hstep : ∀ k, (r k) ^ 2 ≤ (r (k + 1)) ^ 2)
    (hne : ∀ᶠ k in atTop, r k ≠ 0)
    (hinv : Tendsto (fun k => 1 / (r k) ^ 2) atTop (𝓝 0)) :
    (∑' k, qAction n m t (r k) (r (k + 1))) =
      coordinateMismatch n m t (QRamanujanRegularizedConstraints.regularizedCoefficients n m t (r 0)) -
        impossibleCost n m t :=
by
  simpa only [qAction, RiemannResearch.Analysis.RegularizedPathAction.penaltyAction,
    QRamanujanRegularizedConstraints.regularizedCandidate, QRamanujanRegularizedConstraints.regularizedCoefficients,
    map_sub, coordinateMismatch, mismatchEnergy, observe_eq, impossibleCost] using
      total_action_exact (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t r hstep hne hinv

end RiemannResearch.RH.RamanujanInconsistentPenaltyLimits
