/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A single constrained observation and orthogonal projection

Source: user-provided single-head duality handoff, Section 14, for the RH
consumer. The proof is the standard Hilbert-space projection argument; no
claim of novelty is made.

The normalized projection is the minimum-energy vector realizing a prescribed
nonzero observation. This deterministic Hilbert-space identity is used for the
single-coordinate Pareto capacity; it provides no asymptotic arithmetic estimate.
-/

noncomputable section
namespace RiemannResearch.Analysis.SingleObservationProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S : Submodule ℝ H) [S.HasOrthogonalProjection]

theorem projection_pairing (e x : H) (hx : x ∈ S) :
    inner ℝ e x = inner ℝ (S.starProjection e) x := by
  have ho : inner ℝ x (e - S.starProjection e) = 0 :=
    (S.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal e) x hx
  rw [inner_sub_right] at ho
  calc
    _ = inner ℝ x e := real_inner_comm _ _
    _ = inner ℝ x (S.starProjection e) := sub_eq_zero.mp ho
    _ = _ := real_inner_comm _ _

theorem projection_self_pairing (e : H) :
    inner ℝ e (S.starProjection e) = ‖S.starProjection e‖ ^ 2 := by
  rw [projection_pairing S e _ (S.starProjection_apply_mem e),
    real_inner_self_eq_norm_sq]

theorem projection_energy_pos_of_observation (e x : H) (hx : x ∈ S)
    (hobs : inner ℝ e x ≠ 0) : 0 < ‖S.starProjection e‖ ^ 2 := by
  by_contra h
  have hz : ‖S.starProjection e‖ ^ 2 = 0 :=
    le_antisymm (le_of_not_gt h) (sq_nonneg _)
  have hp : S.starProjection e = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  apply hobs
  rw [projection_pairing S e x hx, hp, inner_zero_left]

/-- The scalar multiple of the projection realizing observation `a`. -/
def observationOptimizer (e : H) (a : ℝ) : H :=
  (a / ‖S.starProjection e‖ ^ 2) • S.starProjection e

theorem observationOptimizer_mem (e : H) (a : ℝ) :
    observationOptimizer S e a ∈ S :=
  S.smul_mem _ (S.starProjection_apply_mem e)

theorem observationOptimizer_observation (e : H) (a : ℝ)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0) :
    inner ℝ e (observationOptimizer S e a) = a := by
  rw [observationOptimizer, inner_smul_right, projection_self_pairing]
  exact div_mul_cancel₀ a hq

theorem observationOptimizer_energy (e : H) (a : ℝ)
    (_hq : ‖S.starProjection e‖ ^ 2 ≠ 0) :
    ‖observationOptimizer S e a‖ ^ 2 = a ^ 2 / ‖S.starProjection e‖ ^ 2 := by
  rw [observationOptimizer, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

/-- Exact Pythagorean completion for every feasible vector. -/
theorem observation_energy_completion (e x : H) (a : ℝ)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0)
    (hx : x ∈ S) (hobs : inner ℝ e x = a) :
    ‖x‖ ^ 2 = a ^ 2 / ‖S.starProjection e‖ ^ 2 +
      ‖x - observationOptimizer S e a‖ ^ 2 := by
  have hp : inner ℝ x (observationOptimizer S e a) =
      a ^ 2 / ‖S.starProjection e‖ ^ 2 := by
    have hpx : inner ℝ x (S.starProjection e) = a := by
      calc
        _ = inner ℝ (S.starProjection e) x := real_inner_comm _ _
        _ = inner ℝ e x := (projection_pairing S e x hx).symm
        _ = a := hobs
    rw [observationOptimizer, inner_smul_right, hpx]
    ring
  rw [norm_sub_sq_real, hp, observationOptimizer_energy S e a hq]
  ring

/-- An attained energy minimum, suitable for comparison with covariance minima. -/
theorem observation_energy_isLeast (e : H) (a : ℝ)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0) :
    IsLeast {b : ℝ | ∃ x : H, x ∈ S ∧ inner ℝ e x = a ∧ ‖x‖ ^ 2 = b}
      (a ^ 2 / ‖S.starProjection e‖ ^ 2) := by
  refine ⟨⟨observationOptimizer S e a, observationOptimizer_mem S e a,
    observationOptimizer_observation S e a hq,
    observationOptimizer_energy S e a hq⟩, ?_⟩
  rintro b ⟨x, hx, hobs, rfl⟩
  have hc := observation_energy_completion S e x a hq hx hobs
  nlinarith [sq_nonneg ‖x - observationOptimizer S e a‖]

theorem observationOptimizer_unique (e x : H) (a : ℝ)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0)
    (hx : x ∈ S) (hobs : inner ℝ e x = a) :
    ‖x‖ ^ 2 = a ^ 2 / ‖S.starProjection e‖ ^ 2 ↔
      x = observationOptimizer S e a := by
  constructor
  · intro h
    have hc := observation_energy_completion S e x a hq hx hobs
    have hz : ‖x - observationOptimizer S e a‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · rintro rfl
    exact observationOptimizer_energy S e a hq

/-- Projection deficit is the exact squared distance to the subspace. -/
theorem projection_defect_energy (e : H) :
    ‖e - S.starProjection e‖ ^ 2 = ‖e‖ ^ 2 - ‖S.starProjection e‖ ^ 2 := by
  rw [norm_sub_sq_real, projection_self_pairing]
  ring

/-- When the imposed observation is the target's own energy, its interpolation
error is an exact rational function of the projection deficit. -/
theorem observationOptimizer_error (e : H)
    (hq : ‖S.starProjection e‖ ^ 2 ≠ 0) :
    ‖observationOptimizer S e (‖e‖ ^ 2) - e‖ ^ 2 =
      ‖e‖ ^ 2 * ‖e - S.starProjection e‖ ^ 2 / ‖S.starProjection e‖ ^ 2 := by
  have hp : inner ℝ (observationOptimizer S e (‖e‖ ^ 2)) e = ‖e‖ ^ 2 := by
    rw [real_inner_comm]
    exact observationOptimizer_observation S e (‖e‖ ^ 2) hq
  rw [norm_sub_sq_real, hp, observationOptimizer_energy S e (‖e‖ ^ 2) hq,
    projection_defect_energy]
  have hpne : ‖S.starProjection e‖ ≠ 0 := fun h => hq (by rw [h]; norm_num)
  field_simp [hpne]
  ring

theorem observationOptimizer_orthogonal (S : Submodule ℝ H)
    [S.HasOrthogonalProjection] (y z : H) (a : ℝ)
    (hz : z ∈ S) (hyz : inner ℝ y z = 0) :
    inner ℝ (observationOptimizer S y a) z = 0 := by
  rw [real_inner_comm, observationOptimizer, inner_smul_right]
  have hpz : inner ℝ z (S.starProjection y) = 0 := by
    rw [real_inner_comm, ← projection_pairing S y z hz]
    exact hyz
  rw [hpz, mul_zero]

theorem observation_distance_completion (S : Submodule ℝ H)
    [S.HasOrthogonalProjection] (y f : H) (a : ℝ)
    (hq : ‖S.starProjection y‖ ^ 2 ≠ 0)
    (hf : f ∈ S) (hfy : inner ℝ f y = a) :
    ‖f - y‖ ^ 2 = ‖observationOptimizer S y a - y‖ ^ 2 +
      ‖f - observationOptimizer S y a‖ ^ 2 := by
  have hyf : inner ℝ y f = a := by rw [real_inner_comm]; exact hfy
  have huy : inner ℝ (observationOptimizer S y a) y = a := by
    rw [real_inner_comm]
    exact observationOptimizer_observation S y a hq
  have hc := observation_energy_completion S y f a hq hf hyf
  have hu := observationOptimizer_energy S y a hq
  rw [norm_sub_sq_real, norm_sub_sq_real, hfy, huy]
  linarith

end RiemannResearch.Analysis.SingleObservationProjection
