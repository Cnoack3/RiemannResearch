import RiemannResearch.Analysis.SingleObservationProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Approximation of a target with one prescribed observation

Source: standard Hilbert projection and square completion, applied to the
user-provided CRT exact-prefix optimization record, 2026-09-30. This module
translates the minimum-norm result in `SingleObservationProjection` to an
arbitrary target. The complete norm and its nonnegative remainder are retained.
No asymptotic bound or RH assumption occurs.
-/

noncomputable section
namespace RiemannResearch.Analysis.SingleObservationProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S : Submodule ℝ H) [S.HasOrthogonalProjection]

/-- Project the target and repair the single remaining observation mismatch. -/
def affineObservationOptimizer (e z : H) (a : ℝ) : H :=
  S.starProjection z +
    observationOptimizer S e (a - inner ℝ e (S.starProjection z))

theorem affineObservationOptimizer_mem (e z : H) (a : ℝ) :
    affineObservationOptimizer S e z a ∈ S :=
  S.add_mem (S.starProjection_apply_mem z)
    (observationOptimizer_mem S e _)

theorem affineObservationOptimizer_observation (e z : H) (a : ℝ)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0) :
    inner ℝ e (affineObservationOptimizer S e z a) = a := by
  rw [affineObservationOptimizer, inner_add_right,
    observationOptimizer_observation S e _ hq]
  ring

/-- The target defect is orthogonal to every translated feasible displacement. -/
theorem affine_target_error_split (z x : H) (hx : x ∈ S) :
    ‖z - x‖ ^ 2 = ‖z - S.starProjection z‖ ^ 2 +
      ‖x - S.starProjection z‖ ^ 2 := by
  have hxs : x - S.starProjection z ∈ S :=
    S.sub_mem hx (S.starProjection_apply_mem z)
  have ho : inner ℝ (z - S.starProjection z) (x - S.starProjection z) = 0 := by
    rw [real_inner_comm]
    exact (S.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal z) _ hxs
  have hid : z - x =
      (z - S.starProjection z) - (x - S.starProjection z) := by abel
  rw [hid, norm_sub_sq_real, ho]
  ring

theorem affineObservationOptimizer_energy (e z : H) (a : ℝ)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0) :
    ‖z - affineObservationOptimizer S e z a‖ ^ 2 =
      ‖z - S.starProjection z‖ ^ 2 +
        (a - inner ℝ e (S.starProjection z)) ^ 2 / ‖S.starProjection e‖ ^ 2 := by
  rw [affine_target_error_split S z _ (affineObservationOptimizer_mem S e z a)]
  have hd : affineObservationOptimizer S e z a - S.starProjection z =
      observationOptimizer S e (a - inner ℝ e (S.starProjection z)) := by
    unfold affineObservationOptimizer
    abel
  rw [hd, observationOptimizer_energy S e _ hq]

/-- Exact translated square completion for every feasible vector. -/
theorem affine_observation_error_completion (e z x : H) (a : ℝ)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0)
    (hx : x ∈ S) (hobs : inner ℝ e x = a) :
    ‖z - x‖ ^ 2 =
      ‖z - S.starProjection z‖ ^ 2 +
        (a - inner ℝ e (S.starProjection z)) ^ 2 / ‖S.starProjection e‖ ^ 2 +
      ‖x - affineObservationOptimizer S e z a‖ ^ 2 := by
  have hxs : x - S.starProjection z ∈ S :=
    S.sub_mem hx (S.starProjection_apply_mem z)
  have hobs' : inner ℝ e (x - S.starProjection z) =
      a - inner ℝ e (S.starProjection z) := by
    rw [inner_sub_right, hobs]
  rw [affine_target_error_split S z x hx,
    observation_energy_completion S e _ _ hq hxs hobs']
  have hd : x - S.starProjection z -
      observationOptimizer S e (a - inner ℝ e (S.starProjection z)) =
      x - affineObservationOptimizer S e z a := by
    unfold affineObservationOptimizer
    abel
  rw [hd]
  ring

/-- The scalar formula is an attained complete-error minimum. -/
theorem affine_observation_error_isLeast (e z : H) (a : ℝ)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0) :
    IsLeast {b : ℝ | ∃ x : H, x ∈ S ∧ inner ℝ e x = a ∧ ‖z - x‖ ^ 2 = b}
      (‖z - S.starProjection z‖ ^ 2 +
        (a - inner ℝ e (S.starProjection z)) ^ 2 / ‖S.starProjection e‖ ^ 2) := by
  refine ⟨⟨affineObservationOptimizer S e z a,
    affineObservationOptimizer_mem S e z a,
    affineObservationOptimizer_observation S e z a hq,
    affineObservationOptimizer_energy S e z a hq⟩, ?_⟩
  rintro b ⟨x, hx, hobs, rfl⟩
  have hc := affine_observation_error_completion S e z x a hq hx hobs
  nlinarith [sq_nonneg ‖x - affineObservationOptimizer S e z a‖]

theorem affineObservationOptimizer_unique (e z x : H) (a : ℝ)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0)
    (hx : x ∈ S) (hobs : inner ℝ e x = a) :
    ‖z - x‖ ^ 2 =
      ‖z - S.starProjection z‖ ^ 2 +
        (a - inner ℝ e (S.starProjection z)) ^ 2 / ‖S.starProjection e‖ ^ 2 ↔
      x = affineObservationOptimizer S e z a := by
  constructor
  · intro h
    have hc := affine_observation_error_completion S e z x a hq hx hobs
    have hz : ‖x - affineObservationOptimizer S e z a‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · rintro rfl
    exact affineObservationOptimizer_energy S e z a hq

end RiemannResearch.Analysis.SingleObservationProjection
