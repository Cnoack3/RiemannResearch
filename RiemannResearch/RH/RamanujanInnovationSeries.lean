import RiemannResearch.Analysis.ProjectionInnovationSeries
import RiemannResearch.RH.RamanujanVisitedWalk

/-!
# Full innovation expansions for actually selected Ramanujan conductors

Source: sixth Ramanujan transfer program, 24 October 2026.
Every sequence of conductors gives an unconditional vector series in each
actual measure. Parseval retains the entire unresolved visited-span norm.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanInnovationSeries
open Pareto ZetaTwoHilbert RamanujanVisitedWalk
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionVariation
open RiemannResearch.Analysis.ProjectionInnovationSeries

theorem pareto_innovation_tail_hasSum (draw : ℕ → ℕ) (N : ℕ) :
    HasSum (fun j => paretoCandidate draw (j + N + 1) - paretoCandidate draw (j + N))
      (visitedProjection paretoPacket draw hilbertOne - paretoCandidate draw N) :=
  increment_tail_hasSum paretoPacket draw hilbertOne N

theorem q_innovation_tail_hasSum (draw : ℕ → ℕ) (N : ℕ) :
    HasSum (fun j => qCandidate draw (j + N + 1) - qCandidate draw (j + N))
      (visitedProjection qPacket draw qOne - qCandidate draw N) :=
  increment_tail_hasSum qPacket draw qOne N

theorem pareto_innovation_tail_energy (draw : ℕ → ℕ) (N : ℕ) :
    (∑' j, ‖paretoCandidate draw (j + N + 1) - paretoCandidate draw (j + N)‖ ^ 2) =
      ‖visitedProjection paretoPacket draw hilbertOne - paretoCandidate draw N‖ ^ 2 :=
  increment_tail_energy paretoPacket draw hilbertOne N

theorem q_innovation_tail_energy (draw : ℕ → ℕ) (N : ℕ) :
    (∑' j, ‖qCandidate draw (j + N + 1) - qCandidate draw (j + N)‖ ^ 2) =
      ‖visitedProjection qPacket draw qOne - qCandidate draw N‖ ^ 2 :=
  increment_tail_energy qPacket draw qOne N

/-- Arbitrary finite signed filtering has a diagonal, exact Q energy budget. -/
theorem q_filtered_innovation_energy (draw : ℕ → ℕ) (a : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ j ∈ s, a j • (qCandidate draw (j + 1) - qCandidate draw j)‖ ^ 2 =
      ∑ j ∈ s, (a j) ^ 2 * ‖qCandidate draw (j + 1) - qCandidate draw j‖ ^ 2 :=
  weighted_increment_energy qPacket draw qOne a s

end RiemannResearch.RH.RamanujanInnovationSeries
