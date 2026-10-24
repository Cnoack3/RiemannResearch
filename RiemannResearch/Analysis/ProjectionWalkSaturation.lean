import RiemannResearch.Analysis.ProjectionInnovationSeries
import RiemannResearch.Analysis.ProjectionWalkInexact
import Mathlib.Tactic.Linarith

/-!
# Complete saturation criteria for arbitrary visited dictionaries

Source: sixth Ramanujan transfer program, 24 October 2026.
Cofinal target approximation, captured norm, and total orthogonal gain are
exactly equivalent. No exhaustion hypothesis is needed for this chain.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ProjectionWalkSaturation
open ExhaustiveWalk ProjectionVariation ProjectionInnovationSeries NonnegativeErrorConvergence
variable {H ι α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

theorem visited_energy_split (v : ι → H) (draw : ℕ → ι) (x : H) :
    ‖x‖ ^ 2 = visitedError v draw x + ‖visitedProjection v draw x‖ ^ 2 := by
  simpa only [Submodule.starProjection_bot, ContinuousLinearMap.zero_apply, sub_zero,
    visitedError, visitedProjection] using
      nested_projection_energy (⊥ : Submodule ℝ H) (visitedClosure v draw) bot_le x

theorem total_innovation_energy (v : ι → H) (draw : ℕ → ι) (x : H) :
    (∑' n, ‖increment v draw x n‖ ^ 2) = ‖visitedProjection v draw x‖ ^ 2 := by
  simpa [walkSpan] using increment_tail_energy v draw x 0

theorem gain_saturation_iff (v : ι → H) (draw : ℕ → ι) (x : H) :
    (∑' n, ‖increment v draw x n‖ ^ 2) = ‖x‖ ^ 2 ↔ visitedError v draw x = 0 := by
  rw [total_innovation_energy]
  have he := visited_energy_split v draw x
  constructor <;> intro h <;> linarith

theorem cofinal_norm_zero_iff {l : Filter α} [NeBot l]
    (v : ι → H) (draw : ℕ → ι) (x : H) (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => ‖x - (walkSpan v draw (N i)).starProjection x‖) l (𝓝 0) ↔
      visitedError v draw x = 0 := by
  rw [norm_zero_iff_square]
  have ht : Tendsto (fun i => ‖x - (walkSpan v draw (N i)).starProjection x‖ ^ 2) l
      (𝓝 (visitedError v draw x)) := by
    simpa only [Function.comp_def, walkError] using (walkError_tendsto_visited v draw x).comp hN
  constructor
  · exact fun h => tendsto_nhds_unique ht h
  · intro h
    simpa only [h] using ht

theorem cofinal_mass_iff {l : Filter α} [NeBot l]
    (v : ι → H) (draw : ℕ → ι) (x : H) (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => ‖(walkSpan v draw (N i)).starProjection x‖ ^ 2) l (𝓝 (‖x‖ ^ 2)) ↔
      visitedError v draw x = 0 := by
  have ht : Tendsto (fun i => ‖(walkSpan v draw (N i)).starProjection x‖ ^ 2) l
      (𝓝 (‖visitedProjection v draw x‖ ^ 2)) := by
    simpa only [Function.comp_def] using
      ((walkProjection_tendsto_visited v draw x).comp hN).norm.pow 2
  have he := visited_energy_split v draw x
  constructor
  · intro h
    have hz := tendsto_nhds_unique ht h
    linarith
  · intro h
    have hz : ‖visitedProjection v draw x‖ ^ 2 = ‖x‖ ^ 2 := by linarith
    simpa only [hz] using ht

end RiemannResearch.Analysis.ProjectionWalkSaturation
