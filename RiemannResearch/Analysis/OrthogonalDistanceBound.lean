/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Orthogonal pairings bounded by distance

Source: the user-provided isometric transport handoff, Section 5,
6 November 2026, for this application of projection and Cauchy--Schwarz.
The statement is independent of the Q/P measures; its full-conductor consumer
is QFullCrossedDistances. The initial-interval criterion uses the invariant-subspace
perturbation bounds and exact squared distance below.
-/

noncomputable section

namespace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem infDist_eq_norm_sub_starProjection (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (x : E) : Metric.infDist x (S : Set E) = ‖x - S.starProjection x‖ := by
  simp [Metric.infDist_eq_iInf, S.starProjection_minimal, dist_eq_norm]
theorem infDist_sub_mem (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (x : E) {y : E} (hy : y ∈ S) :
    Metric.infDist (x - y) (S : Set E) = Metric.infDist x (S : Set E) := by
  rw [S.infDist_eq_norm_sub_starProjection, S.infDist_eq_norm_sub_starProjection,
    map_sub, Submodule.starProjection_eq_self_iff.mpr hy]
  congr 1
  abel
theorem infDist_smul_sub_of_mem (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    {x : E} (hx : x ∈ S) (y : E) (c : ℝ) :
    Metric.infDist (c • (x - y)) (S : Set E) =
      |c| * Metric.infDist y (S : Set E) := by
  rw [S.infDist_eq_norm_sub_starProjection, S.infDist_eq_norm_sub_starProjection,
    map_smul, map_sub, Submodule.starProjection_eq_self_iff.mpr hx]
  have he : c • (x - y) - c • (x - S.starProjection y) =
      c • (S.starProjection y - y) := by rw [← smul_sub]; congr 1; abel
  rw [he, norm_smul, Real.norm_eq_abs, norm_sub_rev]

theorem abs_real_inner_le_norm_mul_infDist_of_mem_orthogonal
    (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    {r : E} (hr : r ∈ Sᗮ) (x : E) :
    |inner ℝ r x| ≤ ‖r‖ * Metric.infDist x (S : Set E) := by
  have he : inner ℝ r x = inner ℝ r (x - S.starProjection x) := by
    rw [inner_sub_right, S.inner_left_of_mem_orthogonal (S.starProjection_apply_mem x) hr,
      sub_zero]
  rw [he]
  calc
    _ ≤ ‖r‖ * ‖x - S.starProjection x‖ := abs_real_inner_le_norm _ _
    _ = _ := by
      congr 1
      simp [Metric.infDist_eq_iInf, S.starProjection_minimal, dist_eq_norm]

/-- On the quotient by an invariant subspace the same norm bound holds. -/
theorem infDist_map_le_of_invariant (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (T : E →ₗ[ℝ] E) (hS : ∀ z ∈ S, T z ∈ S) {c : ℝ}
    (hT : ∀ z, ‖T z‖ ≤ c * ‖z‖) (y : E) :
    Metric.infDist (T y) (S : Set E) ≤ c * Metric.infDist y (S : Set E) := by
  calc
    _ ≤ dist (T y) (T (S.starProjection y)) :=
      Metric.infDist_le_dist_of_mem (hS _ (S.starProjection_apply_mem y))
    _ = ‖T (y - S.starProjection y)‖ := by rw [dist_eq_norm, map_sub]
    _ ≤ _ := by rw [S.infDist_eq_norm_sub_starProjection]; exact hT _

/-- Exact square on the quotient, including the component of the image
of the old residual which projects back into the subspace. -/
theorem infDist_sub_map_sq_of_invariant (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (T : E →ₗ[ℝ] E) (hS : ∀ z ∈ S, T z ∈ S) (x y : E) :
    Metric.infDist (x - T y) (S : Set E) ^ 2 =
      Metric.infDist x (S : Set E) ^ 2 + ‖T (y - S.starProjection y)‖ ^ 2 -
        ‖S.starProjection (T (y - S.starProjection y))‖ ^ 2 -
        2 * inner ℝ (x - S.starProjection x) (T (y - S.starProjection y)) := by
  let a := x - S.starProjection x
  let b := T (y - S.starProjection y)
  have hfix : S.starProjection (T (S.starProjection y)) = T (S.starProjection y) :=
    Submodule.starProjection_eq_self_iff.mpr (hS _ (S.starProjection_apply_mem _))
  have hres : (x - T y) - S.starProjection (x - T y) = a - (b - S.starProjection b) := by
    dsimp only [a, b]
    simp only [map_sub, hfix]
    abel
  have hab : inner ℝ a (S.starProjection b) = 0 :=
    S.inner_left_of_mem_orthogonal (S.starProjection_apply_mem b)
      (Submodule.sub_starProjection_mem_orthogonal x)
  have hb : inner ℝ (b - S.starProjection b) (S.starProjection b) = 0 :=
    S.inner_left_of_mem_orthogonal (S.starProjection_apply_mem b)
      (Submodule.sub_starProjection_mem_orthogonal b)
  have hpyth : ‖b - S.starProjection b‖ ^ 2 + ‖S.starProjection b‖ ^ 2 = ‖b‖ ^ 2 := by
    calc
      _ = ‖(b - S.starProjection b) + S.starProjection b‖ ^ 2 := by
        rw [norm_add_sq_real, hb]; ring
      _ = _ := by rw [sub_add_cancel]
  rw [S.infDist_eq_norm_sub_starProjection, S.infDist_eq_norm_sub_starProjection, hres]
  change ‖a - (b - S.starProjection b)‖ ^ 2 =
    ‖a‖ ^ 2 + ‖b‖ ^ 2 - ‖S.starProjection b‖ ^ 2 - 2 * inner ℝ a b
  rw [norm_sub_sq_real, inner_sub_right, hab, sub_zero]
  linarith only [hpyth]

/-- Perturbing one target by the image of another changes quotient distance
by at most the operator bound times the second target's distance. -/
theorem abs_infDist_sub_map_sub_le (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (T : E →ₗ[ℝ] E) (hS : ∀ z ∈ S, T z ∈ S) {c : ℝ}
    (hT : ∀ z, ‖T z‖ ≤ c * ‖z‖) (x y : E) :
    |Metric.infDist (x - T y) (S : Set E) - Metric.infDist x (S : Set E)| ≤
      c * Metric.infDist y (S : Set E) := by
  apply le_trans _ (S.infDist_map_le_of_invariant T hS hT y)
  simp only [S.infDist_eq_norm_sub_starProjection, map_sub]
  let a := x - S.starProjection x
  let b := T y - S.starProjection (T y)
  have he : (x - T y) - (S.starProjection x - S.starProjection (T y)) = a - b := by
    dsimp only [a, b]; abel
  rw [he]
  change |‖a - b‖ - ‖a‖| ≤ ‖b‖
  have h := abs_norm_sub_norm_le (a - b) a
  rwa [show a - b - a = -b by abel, norm_neg] at h

end Submodule
