import RiemannResearch.Analysis.ProjectionWalkComparison
import RiemannResearch.RH.RamanujanVisitedWalk

/-!
# Reordering, repeated conductors, and asynchronous Ramanujan walks

Source: sixth Ramanujan transfer program, 24 October 2026.
Agreement is characterized by the actual target projections, while equality
of visited conductor ranges is a sufficient structural certificate.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.RamanujanWalkComparison
open Pareto ZetaTwoHilbert RamanujanVisitedWalk
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionWalkComparison
variable {α : Type*} {l : Filter α}

theorem pareto_walks_agree_iff [NeBot l] (d e : ℕ → ℕ) (N M : α → ℕ)
    (hN : Tendsto N l atTop) (hM : Tendsto M l atTop) :
    Tendsto (fun i => paretoCandidate d (N i) - paretoCandidate e (M i)) l (𝓝 0) ↔
      visitedProjection paretoPacket d hilbertOne = visitedProjection paretoPacket e hilbertOne :=
  cofinal_difference_zero_iff paretoPacket d e hilbertOne N M hN hM

theorem q_walks_agree_iff [NeBot l] (d e : ℕ → ℕ) (N M : α → ℕ)
    (hN : Tendsto N l atTop) (hM : Tendsto M l atTop) :
    Tendsto (fun i => qCandidate d (N i) - qCandidate e (M i)) l (𝓝 0) ↔
      visitedProjection qPacket d qOne = visitedProjection qPacket e qOne :=
  cofinal_difference_zero_iff qPacket d e qOne N M hN hM

theorem pareto_walks_agree_of_same_range (d e : ℕ → ℕ) (h : Set.range d = Set.range e)
    (N M : α → ℕ) (hN : Tendsto N l atTop) (hM : Tendsto M l atTop) :
    Tendsto (fun i => paretoCandidate d (N i) - paretoCandidate e (M i)) l (𝓝 0) :=
  cofinal_difference_zero_of_same_range paretoPacket d e h hilbertOne N M hN hM

theorem q_walks_agree_of_same_range (d e : ℕ → ℕ) (h : Set.range d = Set.range e)
    (N M : α → ℕ) (hN : Tendsto N l atTop) (hM : Tendsto M l atTop) :
    Tendsto (fun i => qCandidate d (N i) - qCandidate e (M i)) l (𝓝 0) :=
  cofinal_difference_zero_of_same_range qPacket d e h qOne N M hN hM

end RiemannResearch.RH.RamanujanWalkComparison
