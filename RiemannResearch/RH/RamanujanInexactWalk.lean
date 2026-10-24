import RiemannResearch.Analysis.ProjectionWalkInexact
import RiemannResearch.RH.RamanujanVisitedWalk

/-!
# Complete inexact adaptive Ramanujan error budgets

Source: sixth Ramanujan transfer program, 24 October 2026.
Actual Pareto and Q legal iterates need not solve their finite normal equations.
Their errors retain the full legal floor, missed-space square, visited tail,
and solver square separately, and yield exact cofinal convergence criteria.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.RamanujanInexactWalk
open Pareto ZetaTwoHilbert RamanujanVisitedWalk
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionWalkInexact

theorem pareto_full_trial_error (draw : ℕ → ℕ) (n : ℕ) (u : ThresholdHilbert)
    (hu : u ∈ walkSpan paretoPacket draw n) :
    ‖hilbertOne - u‖ ^ 2 = CoefficientStabilization.limitEnergy +
      ‖CoefficientStabilization.limitProjection - visitedProjection paretoPacket draw hilbertOne‖ ^ 2 +
      ‖visitedProjection paretoPacket draw hilbertOne - paretoCandidate draw n‖ ^ 2 +
      ‖paretoCandidate draw n - u‖ ^ 2 := by
  simpa only [limitingError, pareto_dictionaryClosure, CoefficientStabilization.limitEnergy,
    CoefficientStabilization.limitProjection, paretoCandidate] using
      full_trial_error paretoPacket draw hilbertOne u n hu

theorem q_full_trial_error (draw : ℕ → ℕ) (n : ℕ) (u : QHilbert)
    (hu : u ∈ walkSpan qPacket draw n) :
    ‖qOne - u‖ ^ 2 = QRamanujanCanonicalOptimizer.packetLimitEnergy +
      ‖QFullResidueProjection.closure.starProjection qOne - visitedProjection qPacket draw qOne‖ ^ 2 +
      ‖visitedProjection qPacket draw qOne - qCandidate draw n‖ ^ 2 +
      ‖qCandidate draw n - u‖ ^ 2 := by
  simpa only [limitingError, q_dictionaryClosure, QRamanujanCanonicalOptimizer.packetLimitEnergy,
    qCandidate] using full_trial_error qPacket draw qOne u n hu

theorem pareto_trial_tendsto_iff_defect {α : Type*} {l : Filter α}
    (draw : ℕ → ℕ) (N : α → ℕ) (hN : Tendsto N l atTop) (u : α → ThresholdHilbert) :
    Tendsto u l (𝓝 (visitedProjection paretoPacket draw hilbertOne)) ↔
      Tendsto (fun i => ‖paretoCandidate draw (N i) - u i‖) l (𝓝 0) :=
  cofinal_trial_tendsto_iff_defect paretoPacket draw hilbertOne N hN u

theorem q_trial_tendsto_iff_defect {α : Type*} {l : Filter α}
    (draw : ℕ → ℕ) (N : α → ℕ) (hN : Tendsto N l atTop) (u : α → QHilbert) :
    Tendsto u l (𝓝 (visitedProjection qPacket draw qOne)) ↔
      Tendsto (fun i => ‖qCandidate draw (N i) - u i‖) l (𝓝 0) :=
  cofinal_trial_tendsto_iff_defect qPacket draw qOne N hN u

theorem pareto_trial_norm_zero_iff {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (N : α → ℕ) (hN : Tendsto N l atTop) (u : α → ThresholdHilbert)
    (hu : ∀ i, u i ∈ walkSpan paretoPacket draw (N i)) :
    Tendsto (fun i => ‖hilbertOne - u i‖) l (𝓝 0) ↔
      visitedError paretoPacket draw hilbertOne = 0 ∧
        Tendsto (fun i => ‖paretoCandidate draw (N i) - u i‖) l (𝓝 0) :=
  cofinal_trial_norm_zero_iff paretoPacket draw hilbertOne N hN u hu

theorem q_trial_norm_zero_iff {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (N : α → ℕ) (hN : Tendsto N l atTop) (u : α → QHilbert)
    (hu : ∀ i, u i ∈ walkSpan qPacket draw (N i)) :
    Tendsto (fun i => ‖qOne - u i‖) l (𝓝 0) ↔
      visitedError qPacket draw qOne = 0 ∧
        Tendsto (fun i => ‖qCandidate draw (N i) - u i‖) l (𝓝 0) :=
  cofinal_trial_norm_zero_iff qPacket draw qOne N hN u hu

end RiemannResearch.RH.RamanujanInexactWalk
