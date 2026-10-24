import RiemannResearch.Analysis.ProjectionWalkMovingTargets
import RiemannResearch.RH.RamanujanVisitedWalk

/-!
# Stable moving targets for actual Pareto and Q packet walks

Source: sixth Ramanujan transfer program, 24 October 2026.
The actual source may vary with the chosen conductor stage. Strong source
convergence alone suffices; no relation between the two rates is required.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.RamanujanMovingTargets
open Pareto ZetaTwoHilbert RamanujanVisitedWalk
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionWalkMovingTargets
variable {α : Type*} {l : Filter α}

theorem pareto_moving_constant_tendsto (draw : ℕ → ℕ) (N : α → ℕ)
    (hN : Tendsto N l atTop) (F : α → ThresholdHilbert) (hF : Tendsto F l (𝓝 hilbertOne)) :
    Tendsto (fun i => (walkSpan paretoPacket draw (N i)).starProjection (F i)) l
      (𝓝 (visitedProjection paretoPacket draw hilbertOne)) :=
  cofinal_moving_projection_tendsto paretoPacket draw N hN F hilbertOne hF

theorem q_moving_constant_tendsto (draw : ℕ → ℕ) (N : α → ℕ)
    (hN : Tendsto N l atTop) (F : α → QHilbert) (hF : Tendsto F l (𝓝 qOne)) :
    Tendsto (fun i => (walkSpan qPacket draw (N i)).starProjection (F i)) l
      (𝓝 (visitedProjection qPacket draw qOne)) :=
  cofinal_moving_projection_tendsto qPacket draw N hN F qOne hF

theorem pareto_target_perturbation_split (draw : ℕ → ℕ) (n : ℕ) (h : ThresholdHilbert) :
    ‖h‖ ^ 2 =
      ‖(walkSpan paretoPacket draw n).starProjection (hilbertOne + h) - paretoCandidate draw n‖ ^ 2 +
      ‖(hilbertOne + h - (walkSpan paretoPacket draw n).starProjection (hilbertOne + h)) -
        (hilbertOne - paretoCandidate draw n)‖ ^ 2 :=
  target_perturbation_split (walkSpan paretoPacket draw n) hilbertOne h

theorem q_target_perturbation_split (draw : ℕ → ℕ) (n : ℕ) (h : QHilbert) :
    ‖h‖ ^ 2 =
      ‖(walkSpan qPacket draw n).starProjection (qOne + h) - qCandidate draw n‖ ^ 2 +
      ‖(qOne + h - (walkSpan qPacket draw n).starProjection (qOne + h)) -
        (qOne - qCandidate draw n)‖ ^ 2 :=
  target_perturbation_split (walkSpan qPacket draw n) qOne h

end RiemannResearch.RH.RamanujanMovingTargets
