import RiemannResearch.Analysis.RegularizedDuality
import RiemannResearch.RH.QRamanujanRegularizedConstraints

/-!
# Actual Pareto/Q observation duals and complete primal/dual certificates

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
The dual unknowns are signed errors in the actual multiple-transform
coefficients. Neither distinct conductors nor attainability is assumed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanRegularizedDuality
open Pareto ZetaTwoHilbert
open RamanujanRegularizedConstraints (constraintMatrix observe_eq)
open RamanujanCanonicalOptimizer (packetMultipleTransform)
open RiemannResearch.Analysis.FiniteRegularizedConstraints
open RiemannResearch.Analysis.RegularizedDuality
variable {κ : Type*} [Fintype κ]

def paretoDualMultiplier (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) : κ → ℝ :=
  multiplier (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ

def paretoDualValue (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (z : κ → ℝ) : ℝ :=
  dualValue (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ z

theorem pareto_dualMultiplier_coordinate (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (j : κ) :
    paretoDualMultiplier n m t ρ j =
      ρ * (t j - packetMultipleTransform n (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) (m j)) := by
  simp only [paretoDualMultiplier, multiplier, observe_eq, RamanujanRegularizedConstraints.regularizedCoefficients]

/-- The exact physical representer defect and observation defect form the whole duality gap. -/
theorem pareto_primal_dual_gap (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ)
    (a : Fin n → ℝ) (z : κ → ℝ) :
    RamanujanRegularizedConstraints.penalizedError n m t ρ a - paretoDualValue n m t ρ z =
      ‖Fintype.linearCombination ℝ (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (a - RamanujanCanonicalOptimizer.packetCoefficients n) -
        ρ • Fintype.linearCombination ℝ
          (RiemannResearch.Analysis.FiniteGramMultipleConstraint.sourceRows
            (finitePacket_independent n) (constraintMatrix n m)) z‖ ^ 2 +
      ∑ j, (ρ * (packetMultipleTransform n a (m j) - t j) + z j) ^ 2 := by
  simpa only [RamanujanRegularizedConstraints.objective_eq, paretoDualValue, RamanujanCanonicalOptimizer.packetCoefficients, observe_eq] using
    primal_dual_gap (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ a z

theorem pareto_strong_duality (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    RamanujanRegularizedConstraints.penalizedError n m t ρ (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) =
      paretoDualValue n m t ρ (paretoDualMultiplier n m t ρ) := by
  simpa only [RamanujanRegularizedConstraints.objective_eq, RamanujanRegularizedConstraints.regularizedCoefficients,
    paretoDualValue, paretoDualMultiplier] using
      strong_duality (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ

theorem pareto_dual_maximizer_unique (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (z : κ → ℝ) :
    paretoDualValue n m t ρ z = paretoDualValue n m t ρ (paretoDualMultiplier n m t ρ) ↔
      z = paretoDualMultiplier n m t ρ :=
  dual_maximizer_unique (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ z

def qDualMultiplier (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) : κ → ℝ :=
  multiplier (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ

def qDualValue (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (z : κ → ℝ) : ℝ :=
  dualValue (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ z

theorem q_dualMultiplier_coordinate (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (j : κ) :
    qDualMultiplier n m t ρ j =
      ρ * (t j - packetMultipleTransform n (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) (m j)) := by
  simp only [qDualMultiplier, multiplier, observe_eq, QRamanujanRegularizedConstraints.regularizedCoefficients]

/-- The exact physical representer defect and observation defect form the whole duality gap. -/
theorem q_primal_dual_gap (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ)
    (a : Fin n → ℝ) (z : κ → ℝ) :
    QRamanujanRegularizedConstraints.penalizedError n m t ρ a - qDualValue n m t ρ z =
      ‖Fintype.linearCombination ℝ (QRamanujanCanonicalOptimizer.packetFamily n) (a - QRamanujanCanonicalOptimizer.packetCoefficients n) -
        ρ • Fintype.linearCombination ℝ
          (RiemannResearch.Analysis.FiniteGramMultipleConstraint.sourceRows
            (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m)) z‖ ^ 2 +
      ∑ j, (ρ * (packetMultipleTransform n a (m j) - t j) + z j) ^ 2 := by
  simpa only [QRamanujanRegularizedConstraints.objective_eq, qDualValue, QRamanujanCanonicalOptimizer.packetCoefficients, observe_eq] using
    primal_dual_gap (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ a z

theorem q_strong_duality (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    QRamanujanRegularizedConstraints.penalizedError n m t ρ (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) =
      qDualValue n m t ρ (qDualMultiplier n m t ρ) := by
  simpa only [QRamanujanRegularizedConstraints.objective_eq, QRamanujanRegularizedConstraints.regularizedCoefficients,
    qDualValue, qDualMultiplier] using
      strong_duality (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ

theorem q_dual_maximizer_unique (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (z : κ → ℝ) :
    qDualValue n m t ρ z = qDualValue n m t ρ (qDualMultiplier n m t ρ) ↔
      z = qDualMultiplier n m t ρ :=
  dual_maximizer_unique (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ z

end RiemannResearch.RH.RamanujanRegularizedDuality
