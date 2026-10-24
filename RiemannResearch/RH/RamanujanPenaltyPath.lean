import RiemannResearch.Analysis.RegularizedPathAction
import RiemannResearch.RH.QRamanujanRegularizedConstraints

/-!
# Complete action and plateau rigidity of the actual Ramanujan penalty paths

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
Physical and conductor-observation motion are both retained in the exact
finite action. Infinite action is summable even for inconsistent requests.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanPenaltyPath
open Pareto ZetaTwoHilbert
open RamanujanRegularizedConstraints (constraintMatrix coordinateMismatch observe_eq)
open RiemannResearch.Analysis.FiniteRegularizedConstraints
open RiemannResearch.Analysis.RegularizedPathAction
variable {κ : Type*} [Fintype κ]

def paretoAction (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ σ : ℝ) : ℝ :=
  (2 * ‖RamanujanRegularizedConstraints.regularizedCandidate n m t ρ - RamanujanRegularizedConstraints.regularizedCandidate n m t σ‖ ^ 2 +
    (ρ ^ 2 + σ ^ 2) * observationEnergy (constraintMatrix n m)
      (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ - RamanujanRegularizedConstraints.regularizedCoefficients n m t σ)) /
    (σ ^ 2 - ρ ^ 2)

theorem pareto_mismatch_plateau_iff (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ σ : ℝ) :
    coordinateMismatch n m t (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) =
      coordinateMismatch n m t (RamanujanRegularizedConstraints.regularizedCoefficients n m t σ) ↔
      RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ = RamanujanRegularizedConstraints.regularizedCoefficients n m t σ := by
  simpa only [coordinateMismatch, mismatchEnergy, observe_eq, RamanujanRegularizedConstraints.regularizedCoefficients] using
    mismatch_equal_iff_coefficients_equal (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ σ

theorem pareto_finite_action (n : ℕ) (m : κ → ℕ) (t : κ → ℝ)
    (r : ℕ → ℝ) (N : ℕ) (hr : ∀ k < N, (r k) ^ 2 < (r (k + 1)) ^ 2) :
    (∑ k ∈ Finset.range N, paretoAction n m t (r k) (r (k + 1))) =
      coordinateMismatch n m t (RamanujanRegularizedConstraints.regularizedCoefficients n m t (r 0)) -
      coordinateMismatch n m t (RamanujanRegularizedConstraints.regularizedCoefficients n m t (r N)) := by
  simpa only [paretoAction, penaltyAction, coordinateMismatch, mismatchEnergy, observe_eq,
    RamanujanRegularizedConstraints.regularizedCoefficients, RamanujanRegularizedConstraints.regularizedCandidate, map_sub] using
      finite_path_action_exact (finitePacket_independent n) (constraintMatrix n m) hilbertOne t r N hr

theorem pareto_action_summable (n : ℕ) (m : κ → ℕ) (t : κ → ℝ)
    (r : ℕ → ℝ) (hr : ∀ k, (r k) ^ 2 < (r (k + 1)) ^ 2) :
    Summable (fun k => paretoAction n m t (r k) (r (k + 1))) := by
  simpa only [paretoAction, penaltyAction,
    RamanujanRegularizedConstraints.regularizedCoefficients, RamanujanRegularizedConstraints.regularizedCandidate, map_sub] using
      path_action_summable (finitePacket_independent n) (constraintMatrix n m) hilbertOne t r hr

theorem pareto_total_action (n : ℕ) (m : κ → ℕ) (t : κ → ℝ)
    (r : ℕ → ℝ) (hr : ∀ k, (r k) ^ 2 < (r (k + 1)) ^ 2) (L : ℝ)
    (hL : Tendsto (fun k => coordinateMismatch n m t
      (RamanujanRegularizedConstraints.regularizedCoefficients n m t (r k))) atTop (𝓝 L)) :
    (∑' k, paretoAction n m t (r k) (r (k + 1))) =
      coordinateMismatch n m t (RamanujanRegularizedConstraints.regularizedCoefficients n m t (r 0)) - L := by
  have hL' : Tendsto (fun k => mismatchEnergy (constraintMatrix n m) t
      (coefficients (finitePacket_independent n) (constraintMatrix n m) hilbertOne t (r k))) atTop (𝓝 L) := by
    simpa only [mismatchEnergy, observe_eq, coordinateMismatch,
      RamanujanRegularizedConstraints.regularizedCoefficients] using hL
  simpa only [paretoAction, penaltyAction, coordinateMismatch, mismatchEnergy, observe_eq,
    RamanujanRegularizedConstraints.regularizedCoefficients, RamanujanRegularizedConstraints.regularizedCandidate, map_sub] using
      path_action_tsum (finitePacket_independent n) (constraintMatrix n m) hilbertOne t r hr L hL'

def qAction (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ σ : ℝ) : ℝ :=
  (2 * ‖QRamanujanRegularizedConstraints.regularizedCandidate n m t ρ - QRamanujanRegularizedConstraints.regularizedCandidate n m t σ‖ ^ 2 +
    (ρ ^ 2 + σ ^ 2) * observationEnergy (constraintMatrix n m)
      (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ - QRamanujanRegularizedConstraints.regularizedCoefficients n m t σ)) /
    (σ ^ 2 - ρ ^ 2)

theorem q_mismatch_plateau_iff (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ σ : ℝ) :
    coordinateMismatch n m t (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) =
      coordinateMismatch n m t (QRamanujanRegularizedConstraints.regularizedCoefficients n m t σ) ↔
      QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ = QRamanujanRegularizedConstraints.regularizedCoefficients n m t σ := by
  simpa only [coordinateMismatch, mismatchEnergy, observe_eq, QRamanujanRegularizedConstraints.regularizedCoefficients] using
    mismatch_equal_iff_coefficients_equal (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ σ

theorem q_finite_action (n : ℕ) (m : κ → ℕ) (t : κ → ℝ)
    (r : ℕ → ℝ) (N : ℕ) (hr : ∀ k < N, (r k) ^ 2 < (r (k + 1)) ^ 2) :
    (∑ k ∈ Finset.range N, qAction n m t (r k) (r (k + 1))) =
      coordinateMismatch n m t (QRamanujanRegularizedConstraints.regularizedCoefficients n m t (r 0)) -
      coordinateMismatch n m t (QRamanujanRegularizedConstraints.regularizedCoefficients n m t (r N)) := by
  simpa only [qAction, penaltyAction, coordinateMismatch, mismatchEnergy, observe_eq,
    QRamanujanRegularizedConstraints.regularizedCoefficients, QRamanujanRegularizedConstraints.regularizedCandidate, map_sub] using
      finite_path_action_exact (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t r N hr

theorem q_action_summable (n : ℕ) (m : κ → ℕ) (t : κ → ℝ)
    (r : ℕ → ℝ) (hr : ∀ k, (r k) ^ 2 < (r (k + 1)) ^ 2) :
    Summable (fun k => qAction n m t (r k) (r (k + 1))) := by
  simpa only [qAction, penaltyAction,
    QRamanujanRegularizedConstraints.regularizedCoefficients, QRamanujanRegularizedConstraints.regularizedCandidate, map_sub] using
      path_action_summable (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t r hr

theorem q_total_action (n : ℕ) (m : κ → ℕ) (t : κ → ℝ)
    (r : ℕ → ℝ) (hr : ∀ k, (r k) ^ 2 < (r (k + 1)) ^ 2) (L : ℝ)
    (hL : Tendsto (fun k => coordinateMismatch n m t
      (QRamanujanRegularizedConstraints.regularizedCoefficients n m t (r k))) atTop (𝓝 L)) :
    (∑' k, qAction n m t (r k) (r (k + 1))) =
      coordinateMismatch n m t (QRamanujanRegularizedConstraints.regularizedCoefficients n m t (r 0)) - L := by
  have hL' : Tendsto (fun k => mismatchEnergy (constraintMatrix n m) t
      (coefficients (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t (r k))) atTop (𝓝 L) := by
    simpa only [mismatchEnergy, observe_eq, coordinateMismatch,
      QRamanujanRegularizedConstraints.regularizedCoefficients] using hL
  simpa only [qAction, penaltyAction, coordinateMismatch, mismatchEnergy, observe_eq,
    QRamanujanRegularizedConstraints.regularizedCoefficients, QRamanujanRegularizedConstraints.regularizedCandidate, map_sub] using
      path_action_tsum (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t r hr L hL'

end RiemannResearch.RH.RamanujanPenaltyPath
