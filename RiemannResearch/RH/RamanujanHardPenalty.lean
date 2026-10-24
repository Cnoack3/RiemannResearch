import RiemannResearch.Analysis.HardPenaltyGeometry
import RiemannResearch.RH.QRamanujanRegularizedConstraints

/-!
# Quantitative hard-penalty certificates in the actual Ramanujan metrics

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
Each multiplier comes from its own P or Q observation source Gram. The
complete multiplier-square identity yields an O(ρ⁻⁴) coordinate mismatch
bound, improving the earlier O(ρ⁻²) hard-cost comparison.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanHardPenalty

open Pareto ZetaTwoHilbert
open RamanujanRegularizedConstraints (constraintMatrix coordinateMismatch observe_eq)
open RiemannResearch.Analysis.HardPenaltyGeometry
open RiemannResearch.Analysis.FiniteRegularizedConstraints
variable {κ : Type*} [Fintype κ]

def paretoMultiplier (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) : κ → ℝ :=
  hardMultiplier (finitePacket_independent n) (constraintMatrix n (fun j => (e j).val + 2))
    (RamanujanMultipleConstraints.rows_independent n e) hilbertOne t

theorem pareto_multiplier_completion (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (ρ : ℝ) :
    let m := fun j => (e j).val + 2
    let d := RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ -
      RamanujanMultipleConstraints.constrainedCoefficients n e t
    2 * ρ ^ 2 * ‖RamanujanRegularizedConstraints.regularizedCandidate n m t ρ -
      RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 +
      ρ ^ 4 * observationEnergy (constraintMatrix n m) d +
      (∑ j, (ρ ^ 2 * observe (constraintMatrix n m) d j + paretoMultiplier n e t j) ^ 2) =
      ∑ j, (paretoMultiplier n e t j) ^ 2 := by
  have hh : RamanujanMultipleConstraints.constrainedCoefficients n e t =
      RiemannResearch.Analysis.FiniteGramMultipleConstraint.coefficients
        (finitePacket_independent n) (constraintMatrix n (fun j => (e j).val + 2))
        (RamanujanMultipleConstraints.rows_independent n e) hilbertOne t := rfl
  dsimp only [RamanujanRegularizedConstraints.regularizedCandidate,
    RamanujanMultipleConstraints.constrainedCandidate]
  rw [hh]
  simpa only [map_sub, paretoMultiplier,
    RamanujanRegularizedConstraints.regularizedCoefficients, RamanujanRegularizedConstraints.regularizedCandidate,
    RamanujanMultipleConstraints.constrainedCandidate] using
      hard_soft_multiplier_square (finitePacket_independent n)
        (constraintMatrix n (fun j => (e j).val + 2)) (RamanujanMultipleConstraints.rows_independent n e) hilbertOne t ρ

theorem pareto_hard_displacement_bound (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (ρ : ℝ) (hρ : ρ ≠ 0) :
    ‖RamanujanRegularizedConstraints.regularizedCandidate n (fun j => (e j).val + 2) t ρ -
      RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 ≤
      (∑ j, (paretoMultiplier n e t j) ^ 2) / (4 * ρ ^ 2) := by
  have hh : RamanujanMultipleConstraints.constrainedCoefficients n e t =
      RiemannResearch.Analysis.FiniteGramMultipleConstraint.coefficients
        (finitePacket_independent n) (constraintMatrix n (fun j => (e j).val + 2))
        (RamanujanMultipleConstraints.rows_independent n e) hilbertOne t := rfl
  dsimp only [RamanujanRegularizedConstraints.regularizedCandidate,
    RamanujanMultipleConstraints.constrainedCandidate]
  rw [hh]
  simpa only [map_sub, paretoMultiplier,
    RamanujanRegularizedConstraints.regularizedCoefficients, RamanujanRegularizedConstraints.regularizedCandidate,
    RamanujanMultipleConstraints.constrainedCandidate] using
      hard_soft_displacement_bound (finitePacket_independent n)
        (constraintMatrix n (fun j => (e j).val + 2)) (RamanujanMultipleConstraints.rows_independent n e) hilbertOne t ρ hρ

theorem pareto_mismatch_fourth_power_bound (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (ρ : ℝ) (hρ : ρ ≠ 0) :
    coordinateMismatch n (fun j => (e j).val + 2) t
      (RamanujanRegularizedConstraints.regularizedCoefficients n (fun j => (e j).val + 2) t ρ) ≤
      (∑ j, (paretoMultiplier n e t j) ^ 2) / ρ ^ 4 := by
  simpa only [mismatchEnergy, observe_eq, coordinateMismatch, paretoMultiplier,
    RamanujanRegularizedConstraints.regularizedCoefficients] using
      hard_soft_mismatch_bound (finitePacket_independent n)
        (constraintMatrix n (fun j => (e j).val + 2)) (RamanujanMultipleConstraints.rows_independent n e) hilbertOne t ρ hρ

def qMultiplier (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) : κ → ℝ :=
  hardMultiplier (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n (fun j => (e j).val + 2))
    (QRamanujanMultipleConstraints.rows_independent n e) qOne t

theorem q_multiplier_completion (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (ρ : ℝ) :
    let m := fun j => (e j).val + 2
    let d := QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ -
      QRamanujanMultipleConstraints.constrainedCoefficients n e t
    2 * ρ ^ 2 * ‖QRamanujanRegularizedConstraints.regularizedCandidate n m t ρ -
      QRamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 +
      ρ ^ 4 * observationEnergy (constraintMatrix n m) d +
      (∑ j, (ρ ^ 2 * observe (constraintMatrix n m) d j + qMultiplier n e t j) ^ 2) =
      ∑ j, (qMultiplier n e t j) ^ 2 := by
  have hh : QRamanujanMultipleConstraints.constrainedCoefficients n e t =
      RiemannResearch.Analysis.FiniteGramMultipleConstraint.coefficients
        (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n (fun j => (e j).val + 2))
        (QRamanujanMultipleConstraints.rows_independent n e) qOne t := rfl
  dsimp only [QRamanujanRegularizedConstraints.regularizedCandidate,
    QRamanujanMultipleConstraints.constrainedCandidate]
  rw [hh]
  simpa only [map_sub, qMultiplier,
    QRamanujanRegularizedConstraints.regularizedCoefficients, QRamanujanRegularizedConstraints.regularizedCandidate,
    QRamanujanMultipleConstraints.constrainedCandidate] using
      hard_soft_multiplier_square (QRamanujanCanonicalOptimizer.packet_independent n)
        (constraintMatrix n (fun j => (e j).val + 2)) (QRamanujanMultipleConstraints.rows_independent n e) qOne t ρ

theorem q_hard_displacement_bound (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (ρ : ℝ) (hρ : ρ ≠ 0) :
    ‖QRamanujanRegularizedConstraints.regularizedCandidate n (fun j => (e j).val + 2) t ρ -
      QRamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 ≤
      (∑ j, (qMultiplier n e t j) ^ 2) / (4 * ρ ^ 2) := by
  have hh : QRamanujanMultipleConstraints.constrainedCoefficients n e t =
      RiemannResearch.Analysis.FiniteGramMultipleConstraint.coefficients
        (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n (fun j => (e j).val + 2))
        (QRamanujanMultipleConstraints.rows_independent n e) qOne t := rfl
  dsimp only [QRamanujanRegularizedConstraints.regularizedCandidate,
    QRamanujanMultipleConstraints.constrainedCandidate]
  rw [hh]
  simpa only [map_sub, qMultiplier,
    QRamanujanRegularizedConstraints.regularizedCoefficients, QRamanujanRegularizedConstraints.regularizedCandidate,
    QRamanujanMultipleConstraints.constrainedCandidate] using
      hard_soft_displacement_bound (QRamanujanCanonicalOptimizer.packet_independent n)
        (constraintMatrix n (fun j => (e j).val + 2)) (QRamanujanMultipleConstraints.rows_independent n e) qOne t ρ hρ

theorem q_mismatch_fourth_power_bound (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (ρ : ℝ) (hρ : ρ ≠ 0) :
    coordinateMismatch n (fun j => (e j).val + 2) t
      (QRamanujanRegularizedConstraints.regularizedCoefficients n (fun j => (e j).val + 2) t ρ) ≤
      (∑ j, (qMultiplier n e t j) ^ 2) / ρ ^ 4 := by
  simpa only [mismatchEnergy, observe_eq, coordinateMismatch, qMultiplier,
    QRamanujanRegularizedConstraints.regularizedCoefficients] using
      hard_soft_mismatch_bound (QRamanujanCanonicalOptimizer.packet_independent n)
        (constraintMatrix n (fun j => (e j).val + 2)) (QRamanujanMultipleConstraints.rows_independent n e) qOne t ρ hρ

end RiemannResearch.RH.RamanujanHardPenalty
