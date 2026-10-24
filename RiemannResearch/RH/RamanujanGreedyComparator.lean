import RiemannResearch.Analysis.ProjectionGreedyComparator
import RiemannResearch.RH.RamanujanVisitedWalk

/-!
# Actual Ramanujan weak-greedy certificates under Pareto and Q

Source: sixth Ramanujan transfer program, 24 October 2026.
These statements retain the full finite-comparator approximation error and
coefficient budget. The weak-greedy hypothesis is explicit and is not asserted
for an unconstructed selection algorithm.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanGreedyComparator
open Pareto ZetaTwoHilbert RamanujanVisitedWalk
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionVariation
open RiemannResearch.Analysis.ProjectionGreedyComparator

theorem pareto_weakGreedy_complete (draw : ℕ → ℕ) {τ : ℝ}
    (h : WeakGreedy paretoPacket draw hilbertOne τ) :
    visitedProjection paretoPacket draw hilbertOne = CoefficientStabilization.limitProjection := by
  simpa only [pareto_dictionaryClosure, CoefficientStabilization.limitProjection] using
    weakGreedy_complete paretoPacket draw hilbertOne h

theorem q_weakGreedy_complete (draw : ℕ → ℕ) {τ : ℝ}
    (h : WeakGreedy qPacket draw qOne τ) :
    visitedProjection qPacket draw qOne = QFullResidueProjection.closure.starProjection qOne := by
  simpa only [q_dictionaryClosure] using weakGreedy_complete qPacket draw qOne h

theorem pareto_comparator_bound {β : Type*} [Fintype β]
    (draw : ℕ → ℕ) {τ : ℝ} (h : WeakGreedy paretoPacket draw hilbertOne τ)
    (n : ℕ) (index : β → ℕ) (a : β → ℝ) :
    ‖hilbertOne - paretoCandidate draw n‖ ^ 2 ≤
      ‖hilbertOne - paretoCandidate draw n‖ * ‖hilbertOne - ∑ i, a i • paretoPacket (index i)‖ +
        (∑ i, |a i| * (‖paretoPacket (index i)‖ / τ)) *
          ‖paretoCandidate draw (n + 1) - paretoCandidate draw n‖ :=
  weakGreedy_comparator_bound paretoPacket draw hilbertOne h n index a

theorem q_comparator_bound {β : Type*} [Fintype β]
    (draw : ℕ → ℕ) {τ : ℝ} (h : WeakGreedy qPacket draw qOne τ)
    (n : ℕ) (index : β → ℕ) (a : β → ℝ) :
    ‖qOne - qCandidate draw n‖ ^ 2 ≤
      ‖qOne - qCandidate draw n‖ * ‖qOne - ∑ i, a i • qPacket (index i)‖ +
        (∑ i, |a i| * (‖qPacket (index i)‖ / τ)) *
          ‖qCandidate draw (n + 1) - qCandidate draw n‖ :=
  weakGreedy_comparator_bound qPacket draw qOne h n index a

end RiemannResearch.RH.RamanujanGreedyComparator
