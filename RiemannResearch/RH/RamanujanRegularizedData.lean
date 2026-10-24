import RiemannResearch.Analysis.RegularizedDataGeometry
import RiemannResearch.RH.QRamanujanRegularizedConstraints
import RiemannResearch.Analysis.NonnegativeErrorConvergence
import Mathlib.Tactic.Linarith

/-!
# Full Pareto/Q Ramanujan sensitivity to soft coefficient targets

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
The residual of the changed augmented target is retained exactly. The same
finite conductor requests may be repeated or outside the packet stage.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanRegularizedData
open Pareto ZetaTwoHilbert
open RamanujanRegularizedConstraints (constraintMatrix coordinateMismatch observe_eq)
open RiemannResearch.Analysis.FiniteRegularizedConstraints
open RiemannResearch.Analysis.RegularizedDataGeometry

variable {κ : Type*} [Fintype κ]

/-- Exact target sensitivity, including the full augmented data-difference residual. -/
theorem pareto_target_difference_exact (n : ℕ) (m : κ → ℕ)
    (t s : κ → ℝ) (ρ : ℝ) :
    ρ ^ 2 * ∑ j, (t j - s j) ^ 2 =
      ‖RamanujanRegularizedConstraints.regularizedCandidate n m t ρ -
        RamanujanRegularizedConstraints.regularizedCandidate n m s ρ‖ ^ 2 +
      ρ ^ 2 * observationEnergy (constraintMatrix n m)
        (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ -
          RamanujanRegularizedConstraints.regularizedCoefficients n m s ρ) +
      objective (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (constraintMatrix n m) 0 (t - s) ρ
        (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ -
          RamanujanRegularizedConstraints.regularizedCoefficients n m s ρ) := by
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    RamanujanRegularizedConstraints.regularizedCoefficients,
    RamanujanRegularizedConstraints.regularizedCandidate, map_sub] using
      data_difference_exact (finitePacket_independent n) (constraintMatrix n m)
        hilbertOne hilbertOne t s ρ

theorem q_target_difference_exact (n : ℕ) (m : κ → ℕ)
    (t s : κ → ℝ) (ρ : ℝ) :
    ρ ^ 2 * ∑ j, (t j - s j) ^ 2 =
      ‖QRamanujanRegularizedConstraints.regularizedCandidate n m t ρ -
        QRamanujanRegularizedConstraints.regularizedCandidate n m s ρ‖ ^ 2 +
      ρ ^ 2 * observationEnergy (constraintMatrix n m)
        (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ -
          QRamanujanRegularizedConstraints.regularizedCoefficients n m s ρ) +
      objective (QRamanujanCanonicalOptimizer.packetFamily n)
        (constraintMatrix n m) 0 (t - s) ρ
        (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ -
          QRamanujanRegularizedConstraints.regularizedCoefficients n m s ρ) := by
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    QRamanujanRegularizedConstraints.regularizedCoefficients,
    QRamanujanRegularizedConstraints.regularizedCandidate, map_sub] using
      data_difference_exact (QRamanujanCanonicalOptimizer.packet_independent n)
        (constraintMatrix n m) qOne qOne t s ρ

theorem pareto_target_displacement_bound (n : ℕ) (m : κ → ℕ)
    (t s : κ → ℝ) (ρ : ℝ) :
    ‖RamanujanRegularizedConstraints.regularizedCandidate n m t ρ -
      RamanujanRegularizedConstraints.regularizedCandidate n m s ρ‖ ^ 2 ≤
      ρ ^ 2 * ∑ j, (t j - s j) ^ 2 := by
  have h := data_difference_bound (finitePacket_independent n)
    (constraintMatrix n m) hilbertOne hilbertOne t s ρ
  have hp := mul_nonneg (sq_nonneg ρ)
    (observationEnergy_nonneg (constraintMatrix n m)
      (coefficients (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ -
        coefficients (finitePacket_independent n) (constraintMatrix n m) hilbertOne s ρ))
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  change ‖Fintype.linearCombination ℝ _ _ - Fintype.linearCombination ℝ _ _‖ ^ 2 ≤ _
  rw [← map_sub]
  dsimp only [RamanujanRegularizedConstraints.regularizedCoefficients]
  linarith

theorem q_target_displacement_bound (n : ℕ) (m : κ → ℕ)
    (t s : κ → ℝ) (ρ : ℝ) :
    ‖QRamanujanRegularizedConstraints.regularizedCandidate n m t ρ -
      QRamanujanRegularizedConstraints.regularizedCandidate n m s ρ‖ ^ 2 ≤
      ρ ^ 2 * ∑ j, (t j - s j) ^ 2 := by
  have h := data_difference_bound (QRamanujanCanonicalOptimizer.packet_independent n)
    (constraintMatrix n m) qOne qOne t s ρ
  have hp := mul_nonneg (sq_nonneg ρ)
    (observationEnergy_nonneg (constraintMatrix n m)
      (coefficients (QRamanujanCanonicalOptimizer.packet_independent n)
        (constraintMatrix n m) qOne t ρ -
        coefficients (QRamanujanCanonicalOptimizer.packet_independent n)
          (constraintMatrix n m) qOne s ρ))
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  change ‖Fintype.linearCombination ℝ _ _ - Fintype.linearCombination ℝ _ _‖ ^ 2 ≤ _
  rw [← map_sub]
  dsimp only [QRamanujanRegularizedConstraints.regularizedCoefficients]
  linarith

/-- Stages, rows and penalties may all move; only their actual weighted target error is needed. -/
theorem q_moving_target_stability {α : Type*} {l : Filter α}
    (N : α → ℕ) (m : α → κ → ℕ) (t s : α → κ → ℝ) (ρ : α → ℝ)
    (h : Tendsto (fun i => (ρ i) ^ 2 * ∑ j, (t i j - s i j) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => ‖QRamanujanRegularizedConstraints.regularizedCandidate
      (N i) (m i) (t i) (ρ i) - QRamanujanRegularizedConstraints.regularizedCandidate
      (N i) (m i) (s i) (ρ i)‖ ^ 2) l (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall (fun i => sq_nonneg _))
    (Eventually.of_forall (fun i => q_target_displacement_bound (N i) (m i) (t i) (s i) (ρ i))) h

theorem pareto_moving_target_stability {α : Type*} {l : Filter α}
    (N : α → ℕ) (m : α → κ → ℕ) (t s : α → κ → ℝ) (ρ : α → ℝ)
    (h : Tendsto (fun i => (ρ i) ^ 2 * ∑ j, (t i j - s i j) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => ‖RamanujanRegularizedConstraints.regularizedCandidate
      (N i) (m i) (t i) (ρ i) - RamanujanRegularizedConstraints.regularizedCandidate
      (N i) (m i) (s i) (ρ i)‖ ^ 2) l (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall (fun i => sq_nonneg _))
    (Eventually.of_forall (fun i => pareto_target_displacement_bound (N i) (m i) (t i) (s i) (ρ i))) h

end RiemannResearch.RH.RamanujanRegularizedData
