/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Abel

/-!
# Orthogonal pairings bounded by distance

Source: the user-provided isometric transport handoff, Section 5,
6 November 2026, for this application of projection and Cauchy--Schwarz.
The statement is independent of the Q/P measures; its full-conductor consumer
is QFullCrossedDistances.
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
end Submodule
