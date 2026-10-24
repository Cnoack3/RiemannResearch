import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moving targets along arbitrary projection dictionaries

Source: sixth Ramanujan transfer program, 24 October 2026.
Target perturbations split exactly between fitted and residual components.
Uniform contraction permits independent target and dictionary limits.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.ProjectionWalkMovingTargets
open ExhaustiveWalk
variable {H ι α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

theorem residual_perturbation_exact (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (x h : H) :
    ‖x + h - K.starProjection (x + h)‖ ^ 2 =
      ‖x - K.starProjection x‖ ^ 2 +
      2 * inner ℝ (x - K.starProjection x) (h - K.starProjection h) +
      ‖h - K.starProjection h‖ ^ 2 := by
  have he : x + h - K.starProjection (x + h) =
      (x - K.starProjection x) + (h - K.starProjection h) := by rw [map_add]; abel
  rw [he, norm_add_sq_real]

/-- Exact allocation of a target perturbation between the fitted and residual changes. -/
theorem target_perturbation_split (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (x h : H) :
    ‖h‖ ^ 2 = ‖K.starProjection (x + h) - K.starProjection x‖ ^ 2 +
      ‖(x + h - K.starProjection (x + h)) - (x - K.starProjection x)‖ ^ 2 := by
  have he := nested_projection_energy (⊥ : Submodule ℝ H) K bot_le h
  simp only [Submodule.starProjection_bot, ContinuousLinearMap.zero_apply, sub_zero] at he
  have hp : K.starProjection (x + h) - K.starProjection x = K.starProjection h := by
    rw [map_add]; abel
  have hr : (x + h - K.starProjection (x + h)) - (x - K.starProjection x) =
      h - K.starProjection h := by rw [map_add]; abel
  rw [hp, hr]
  linarith

theorem residual_perturbation_energy_bound (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (x h : H) :
    |‖x + h - K.starProjection (x + h)‖ ^ 2 - ‖x - K.starProjection x‖ ^ 2| ≤
      2 * ‖x - K.starProjection x‖ * ‖h‖ + ‖h‖ ^ 2 := by
  have he := residual_perturbation_exact K x h
  have hh := nested_projection_energy (⊥ : Submodule ℝ H) K bot_le h
  simp only [Submodule.starProjection_bot, ContinuousLinearMap.zero_apply, sub_zero] at hh
  have hr : ‖h - K.starProjection h‖ ≤ ‖h‖ := by
    nlinarith [sq_nonneg ‖K.starProjection h‖, norm_nonneg (h - K.starProjection h), norm_nonneg h]
  have hc := abs_real_inner_le_norm (x - K.starProjection x) (h - K.starProjection h)
  have hc' := hc.trans (mul_le_mul_of_nonneg_left hr (norm_nonneg _))
  have hc₁ := (abs_le.mp hc').1
  have hc₂ := (abs_le.mp hc').2
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg ‖h - K.starProjection h‖, sq_nonneg ‖K.starProjection h‖]

/-- The source and the stage may converge along any common filter, with no rate coupling. -/
theorem cofinal_moving_projection_tendsto {l : Filter α}
    (v : ι → H) (draw : ℕ → ι) (N : α → ℕ) (hN : Tendsto N l atTop)
    (F : α → H) (x : H) (hF : Tendsto F l (𝓝 x)) :
    Tendsto (fun i => (walkSpan v draw (N i)).starProjection (F i)) l
      (𝓝 (visitedProjection v draw x)) := by
  have hx : Tendsto (fun i => (walkSpan v draw (N i)).starProjection x) l
      (𝓝 (visitedProjection v draw x)) := by
    simpa only [Function.comp_def] using (walkProjection_tendsto_visited v draw x).comp hN
  apply tendsto_of_tendsto_of_dist hx
  have hconst : Tendsto (fun _ : α => x) l (𝓝 x) := tendsto_const_nhds
  have he : Tendsto (fun i => ‖x - F i‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hconst.sub hF).norm
  apply squeeze_zero (fun i => dist_nonneg) _ he
  intro i
  rw [dist_eq_norm, ← map_sub]
  exact (walkSpan v draw (N i)).norm_starProjection_apply_le (x - F i)

theorem cofinal_moving_residual_tendsto {l : Filter α}
    (v : ι → H) (draw : ℕ → ι) (N : α → ℕ) (hN : Tendsto N l atTop)
    (F : α → H) (x : H) (hF : Tendsto F l (𝓝 x)) :
    Tendsto (fun i => F i - (walkSpan v draw (N i)).starProjection (F i)) l
      (𝓝 (x - visitedProjection v draw x)) :=
  hF.sub (cofinal_moving_projection_tendsto v draw N hN F x hF)

theorem cofinal_moving_error_tendsto {l : Filter α}
    (v : ι → H) (draw : ℕ → ι) (N : α → ℕ) (hN : Tendsto N l atTop)
    (F : α → H) (x : H) (hF : Tendsto F l (𝓝 x)) :
    Tendsto (fun i => ‖F i - (walkSpan v draw (N i)).starProjection (F i)‖ ^ 2) l
      (𝓝 (visitedError v draw x)) :=
  (cofinal_moving_residual_tendsto v draw N hN F x hF).norm.pow 2

end RiemannResearch.Analysis.ProjectionWalkMovingTargets
