import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.ProjectionTrialEnergy
import RiemannResearch.Analysis.NonnegativeErrorConvergence
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Inexact legal solves on arbitrary visited dictionaries

Source: sixth Ramanujan transfer program, 24 October 2026.
The full error has four separate exact squares: the full legal-space floor,
the missed-span defect, the still-unvisited tail, and the solver defect.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.ProjectionWalkInexact
open ExhaustiveWalk NonnegativeErrorConvergence
variable {H ι α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

theorem full_trial_error (v : ι → H) (draw : ℕ → ι) (x u : H) (n : ℕ)
    (hu : u ∈ walkSpan v draw n) :
    ‖x - u‖ ^ 2 = limitingError v x +
      ‖(ExhaustiveWalk.dictionaryClosure v).starProjection x - visitedProjection v draw x‖ ^ 2 +
      ‖visitedProjection v draw x - (walkSpan v draw n).starProjection x‖ ^ 2 +
      ‖(walkSpan v draw n).starProjection x - u‖ ^ 2 := by
  have ht := projection_trial_energy (walkSpan v draw n) x u hu
  have hw := walkError_eq_visited_add v draw x n
  have hv := visitedError_eq_full_add v draw x
  change ‖x - (walkSpan v draw n).starProjection x‖ ^ 2 = _ at hw
  linarith

/-- Strong convergence to the visited fit is exactly vanishing solver defect. -/
theorem cofinal_trial_tendsto_iff_defect {l : Filter α}
    (v : ι → H) (draw : ℕ → ι) (x : H) (N : α → ℕ) (hN : Tendsto N l atTop)
    (u : α → H) :
    Tendsto u l (𝓝 (visitedProjection v draw x)) ↔
      Tendsto (fun i => ‖(walkSpan v draw (N i)).starProjection x - u i‖) l (𝓝 0) := by
  have hp : Tendsto (fun i => (walkSpan v draw (N i)).starProjection x) l
      (𝓝 (visitedProjection v draw x)) := by
    simpa only [Function.comp_def] using (walkProjection_tendsto_visited v draw x).comp hN
  constructor
  · intro hu
    simpa only [sub_self, norm_zero] using (hp.sub hu).norm
  · intro hu
    have hz := tendsto_zero_iff_norm_tendsto_zero.mpr hu
    have hf : u = fun i => (walkSpan v draw (N i)).starProjection x -
        ((walkSpan v draw (N i)).starProjection x - u i) := by
      funext i
      abel
    rw [hf]
    simpa only [sub_zero] using hp.sub hz

/-- Cofinal legal inexact trials reach the target iff both visited saturation and solver accuracy hold. -/
theorem cofinal_trial_norm_zero_iff {l : Filter α} [NeBot l]
    (v : ι → H) (draw : ℕ → ι) (x : H) (N : α → ℕ) (hN : Tendsto N l atTop)
    (u : α → H) (hu : ∀ i, u i ∈ walkSpan v draw (N i)) :
    Tendsto (fun i => ‖x - u i‖) l (𝓝 0) ↔
      visitedError v draw x = 0 ∧
        Tendsto (fun i => ‖(walkSpan v draw (N i)).starProjection x - u i‖) l (𝓝 0) := by
  have he : Tendsto (fun i => walkError v draw x (N i)) l (𝓝 (visitedError v draw x)) := by
    simpa only [Function.comp_def] using (walkError_tendsto_visited v draw x).comp hN
  have he0 : Tendsto (fun i => walkError v draw x (N i)) l (𝓝 0) ↔
      visitedError v draw x = 0 := by
    constructor
    · exact fun h => tendsto_nhds_unique he h
    · intro h
      simpa only [h] using he
  rw [norm_zero_iff_square]
  have ht : (fun i => ‖x - u i‖ ^ 2) = fun i => walkError v draw x (N i) +
      ‖(walkSpan v draw (N i)).starProjection x - u i‖ ^ 2 := by
    funext i
    exact projection_trial_energy (walkSpan v draw (N i)) x (u i) (hu i)
  rw [ht, nonnegative_add_zero_iff
    (fun i => walkError v draw x (N i))
    (fun i => ‖(walkSpan v draw (N i)).starProjection x - u i‖ ^ 2)
    (fun i => sq_nonneg _) (fun i => sq_nonneg _)]
  exact and_congr he0 (norm_zero_iff_square _).symm

end RiemannResearch.Analysis.ProjectionWalkInexact
