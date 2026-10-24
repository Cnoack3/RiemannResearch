import RiemannResearch.Analysis.ProjectionCorrelationCompleteness
import RiemannResearch.RH.RamanujanVisitedWalk

/-!
# Adaptive completeness for the actual Pareto and Q Ramanujan dictionaries

Source: sixth Ramanujan transfer program, 24 October 2026.
Vanishing correlations with every legal packet are precisely what removes the
missed-span defect. This permits non-exhaustive, repeated, adaptive selections.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.RamanujanCorrelationCompleteness
open Pareto ZetaTwoHilbert RamanujanVisitedWalk
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionCorrelationCompleteness

theorem pareto_adaptive_complete_iff (draw : ℕ → ℕ) :
    visitedProjection paretoPacket draw hilbertOne = CoefficientStabilization.limitProjection ↔
      ∀ j, Tendsto (fun n => inner ℝ (paretoPacket j) (hilbertOne - paretoCandidate draw n))
        atTop (𝓝 0) := by
  simpa only [CorrelationsVanish, paretoCandidate, pareto_dictionaryClosure,
    CoefficientStabilization.limitProjection] using
      visited_eq_full_iff_correlations paretoPacket draw hilbertOne

theorem q_adaptive_complete_iff (draw : ℕ → ℕ) :
    visitedProjection qPacket draw qOne = QFullResidueProjection.closure.starProjection qOne ↔
      ∀ j, Tendsto (fun n => inner ℝ (qPacket j) (qOne - qCandidate draw n))
        atTop (𝓝 0) := by
  simpa only [CorrelationsVanish, qCandidate, q_dictionaryClosure] using
    visited_eq_full_iff_correlations qPacket draw qOne

theorem pareto_adaptive_error_iff (draw : ℕ → ℕ) :
    visitedError paretoPacket draw hilbertOne = CoefficientStabilization.limitEnergy ↔
      CorrelationsVanish paretoPacket draw hilbertOne := by
  simpa only [limitingError, pareto_dictionaryClosure, CoefficientStabilization.limitEnergy,
    CoefficientStabilization.limitProjection] using
      error_eq_full_iff_correlations paretoPacket draw hilbertOne

theorem q_adaptive_error_iff (draw : ℕ → ℕ) :
    visitedError qPacket draw qOne = QRamanujanCanonicalOptimizer.packetLimitEnergy ↔
      CorrelationsVanish qPacket draw qOne := by
  simpa only [limitingError, q_dictionaryClosure, QRamanujanCanonicalOptimizer.packetLimitEnergy]
    using error_eq_full_iff_correlations qPacket draw qOne

end RiemannResearch.RH.RamanujanCorrelationCompleteness
