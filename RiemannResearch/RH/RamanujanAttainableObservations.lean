import RiemannResearch.Analysis.AttainableObservations
import RiemannResearch.RH.QRamanujanRegularizedConstraints

/-!
# Exact correction of inconsistent Pareto/Q Ramanujan coefficient requests

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
The actual packet multiple-transform matrix determines all attainable
requests, including repeated conductors and conductors outside the stage.
The same arithmetic impossibility cost applies to both Hilbert measures.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanAttainableObservations
open Pareto ZetaTwoHilbert
open RamanujanRegularizedConstraints (constraintMatrix coordinateMismatch observe_eq)
open RamanujanCanonicalOptimizer (packetMultipleTransform)
open RiemannResearch.Analysis.FiniteRegularizedConstraints
open RiemannResearch.Analysis.AttainableObservations
variable {κ : Type*} [Fintype κ]

def attainableTargets (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) : κ → ℝ :=
  projectedTarget (constraintMatrix n m) t

def impossibleCost (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) : ℝ :=
  inconsistency (constraintMatrix n m) t

theorem attainableTargets_feasible (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) :
    ∃ a : Fin n → ℝ, ∀ j, packetMultipleTransform n a (m j) = attainableTargets n m t j := by
  simpa only [observe_eq, attainableTargets] using projectedTarget_feasible (constraintMatrix n m) t

/-- Complete mismatch consists of an irreducible arithmetic cost and an attainable cost. -/
theorem coordinateMismatch_decomposition (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (a : Fin n → ℝ) :
    coordinateMismatch n m t a = impossibleCost n m t +
      coordinateMismatch n m (attainableTargets n m t) a := by
  simpa only [mismatchEnergy, observe_eq, coordinateMismatch, impossibleCost,
    attainableTargets] using mismatch_decomposition (constraintMatrix n m) t a

theorem impossibleCost_zero_iff (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) :
    impossibleCost n m t = 0 ↔
      ∃ a : Fin n → ℝ, ∀ j, packetMultipleTransform n a (m j) = t j := by
  simpa only [impossibleCost, observe_eq] using inconsistency_zero_iff (constraintMatrix n m) t

theorem pareto_coefficients_attainable (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ =
      RamanujanRegularizedConstraints.regularizedCoefficients n m (attainableTargets n m t) ρ :=
  coefficients_projectedTarget (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ

theorem q_coefficients_attainable (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ =
      QRamanujanRegularizedConstraints.regularizedCoefficients n m (attainableTargets n m t) ρ :=
  coefficients_projectedTarget (QRamanujanCanonicalOptimizer.packet_independent n)
    (constraintMatrix n m) qOne t ρ

/-- Impossible requests contribute exactly the weighted impossible cost to the optimum. -/
theorem pareto_minimum_decomposition (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    RamanujanRegularizedConstraints.penalizedError n m t ρ
      (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) =
    RamanujanRegularizedConstraints.penalizedError n m (attainableTargets n m t) ρ
      (RamanujanRegularizedConstraints.regularizedCoefficients n m (attainableTargets n m t) ρ) +
      ρ ^ 2 * impossibleCost n m t := by
  have h := objective_decomposition
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (constraintMatrix n m) hilbertOne t ρ
    (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ)
  simp only [RamanujanRegularizedConstraints.objective_eq] at h
  calc
    _ = RamanujanRegularizedConstraints.penalizedError n m (attainableTargets n m t) ρ
        (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) +
        ρ ^ 2 * impossibleCost n m t := h
    _ = _ := by rw [pareto_coefficients_attainable n m t ρ]

theorem q_minimum_decomposition (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    QRamanujanRegularizedConstraints.penalizedError n m t ρ
      (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) =
    QRamanujanRegularizedConstraints.penalizedError n m (attainableTargets n m t) ρ
      (QRamanujanRegularizedConstraints.regularizedCoefficients n m (attainableTargets n m t) ρ) +
      ρ ^ 2 * impossibleCost n m t := by
  have h := objective_decomposition (QRamanujanCanonicalOptimizer.packetFamily n)
    (constraintMatrix n m) qOne t ρ
    (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ)
  simp only [QRamanujanRegularizedConstraints.objective_eq] at h
  calc
    _ = QRamanujanRegularizedConstraints.penalizedError n m (attainableTargets n m t) ρ
        (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) +
        ρ ^ 2 * impossibleCost n m t := h
    _ = _ := by rw [q_coefficients_attainable n m t ρ]

end RiemannResearch.RH.RamanujanAttainableObservations
