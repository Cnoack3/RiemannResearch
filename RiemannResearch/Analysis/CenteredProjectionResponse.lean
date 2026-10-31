/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import RiemannResearch.Analysis.DenseProjectionTesting
import RiemannResearch.Analysis.NestedProjectionPairing
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Centered signed projection responses with exact loss

Source: SquarefreeShortHeadSchurResearch20261030.md, section 4.
The joint ellipse is the user-requested refinement developed on 31 October 2026.
All equalities retain the orthogonal loss square and the signed residual term.
The squarefree application is RH.QSquarefreeShortHeadResponse.
-/

noncomputable section
namespace RiemannResearch.Analysis.CenteredProjectionResponse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def center (r z : E) : E := z - (inner ℝ r z / ‖r‖ ^ 2) • r

theorem center_inner (r z : E) (hr : ‖r‖ ^ 2 ≠ 0) :
    inner ℝ r (center r z) = 0 := by
  rw [center, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ hr, sub_self]

theorem center_norm_sq (r z : E) (_hr : ‖r‖ ^ 2 ≠ 0) :
    ‖center r z‖ ^ 2 = ‖z‖ ^ 2 - (inner ℝ r z) ^ 2 / ‖r‖ ^ 2 := by
  rw [center, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_right, real_inner_comm z r]
  field_simp [_hr]
  ring

variable (S : Submodule ℝ E) [S.HasOrthogonalProjection]
open ResidualizedProjectionKernel

theorem projection_center (r z : E) (hr : r ∈ Sᗮ) :
    S.starProjection (center r z) = S.starProjection z := by
  rw [center, map_sub, map_smul,
    S.starProjection_apply_eq_zero_iff.mpr hr, smul_zero, sub_zero]

def sourceLoss (r z : E) : E := center r z - S.starProjection (center r z)

theorem source_variance_exact (r z : E) (hr : r ∈ Sᗮ)
    (hr0 : ‖r‖ ^ 2 ≠ 0) :
    ‖S.starProjection z‖ ^ 2 =
      ‖z‖ ^ 2 - (inner ℝ r z) ^ 2 / ‖r‖ ^ 2 - ‖sourceLoss S r z‖ ^ 2 := by
  have h := residual_norm_sq S (center r z)
  rw [center_norm_sq r z hr0, projection_center S r z hr] at h
  rw [sourceLoss, projection_center S r z hr]
  linarith

theorem complement_center_mem (r e : E) (hr : r ∈ Sᗮ) :
    center r (e - S.starProjection e) ∈ Sᗮ := by
  exact S.orthogonal.sub_mem
    (Submodule.sub_starProjection_mem_orthogonal e)
    (S.orthogonal.smul_mem _ hr)

theorem complement_center_norm_sq (r e : E) (hr : r ∈ Sᗮ)
    (hr0 : ‖r‖ ^ 2 ≠ 0) :
    ‖center r (e - S.starProjection e)‖ ^ 2 =
      ‖e‖ ^ 2 - ‖S.starProjection e‖ ^ 2 -
        (inner ℝ r e) ^ 2 / ‖r‖ ^ 2 := by
  rw [center_norm_sq r _ hr0, residual_norm_sq S e, inner_sub_right,
    orthogonal_inner_projection S hr e, sub_zero]

theorem signed_complement_exact (r e z : E) (hr : r ∈ Sᗮ)
    (hr0 : ‖r‖ ^ 2 ≠ 0) (hez : inner ℝ e z = 0) :
    inner ℝ (S.starProjection e) z +
        inner ℝ r e * inner ℝ r z / ‖r‖ ^ 2 =
      - inner ℝ (center r (e - S.starProjection e)) (sourceLoss S r z) := by
  have ho := complement_center_mem S r e hr
  have hor : inner ℝ (center r (e - S.starProjection e)) r = 0 := by
    rw [real_inner_comm]
    exact center_inner r _ hr0
  rw [sourceLoss, inner_sub_right,
    orthogonal_inner_projection S ho (center r z), sub_zero]
  rw [show center r z = z - (inner ℝ r z / ‖r‖ ^ 2) • r from rfl,
    inner_sub_right, real_inner_smul_right, hor, mul_zero, sub_zero]
  rw [center, inner_sub_left, real_inner_smul_left, inner_sub_left, hez,
    inner_sub_right, orthogonal_inner_projection S hr e, sub_zero]
  ring

theorem response_sq_le_source_variance (r e z : E) (hr : r ∈ Sᗮ)
    (hr0 : ‖r‖ ^ 2 ≠ 0) :
    (inner ℝ (S.starProjection e) z) ^ 2 ≤
      ‖S.starProjection e‖ ^ 2 *
        (‖z‖ ^ 2 - (inner ℝ r z) ^ 2 / ‖r‖ ^ 2 - ‖sourceLoss S r z‖ ^ 2) := by
  rw [← source_variance_exact S r z hr hr0,
    DenseProjectionTesting.inner_eq_projected_test S (S.starProjection_apply_mem e) z]
  exact NestedProjectionPairing.real_pairing_sq_le _ _

theorem signed_complement_sq_le (r e z : E) (hr : r ∈ Sᗮ)
    (hr0 : ‖r‖ ^ 2 ≠ 0) (hez : inner ℝ e z = 0) :
    (inner ℝ (S.starProjection e) z +
        inner ℝ r e * inner ℝ r z / ‖r‖ ^ 2) ^ 2 ≤
      (‖e‖ ^ 2 - ‖S.starProjection e‖ ^ 2 -
        (inner ℝ r e) ^ 2 / ‖r‖ ^ 2) * ‖sourceLoss S r z‖ ^ 2 := by
  rw [signed_complement_exact S r e z hr hr0 hez, neg_sq,
    ← complement_center_norm_sq S r e hr hr0]
  exact NestedProjectionPairing.real_pairing_sq_le _ _

/-- Combining both projection channels gives a denominator-free ellipse.
The negative correction and both channels are retained. -/
theorem joint_bound_of_two_channels (t a K L V d : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hp : t ^ 2 ≤ K * (V - d)) (hc : (t + a) ^ 2 ≤ L * d) :
    ((K + L) * t + K * a) ^ 2 ≤ K * L * ((K + L) * V - a ^ 2) := by
  have h1 := mul_le_mul_of_nonneg_left hp hL
  have h2 := mul_le_mul_of_nonneg_left hc hK
  have h3 : L * t ^ 2 + K * (t + a) ^ 2 ≤ K * L * V := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 (add_nonneg hK hL)
  nlinarith

theorem response_joint_bound (r e z : E) (hr : r ∈ Sᗮ)
    (hr0 : ‖r‖ ^ 2 ≠ 0) (hez : inner ℝ e z = 0) :
    let K := ‖S.starProjection e‖ ^ 2
    let L := ‖e‖ ^ 2 - K - (inner ℝ r e) ^ 2 / ‖r‖ ^ 2
    let a := inner ℝ r e * inner ℝ r z / ‖r‖ ^ 2
    let V := ‖z‖ ^ 2 - (inner ℝ r z) ^ 2 / ‖r‖ ^ 2
    ((K + L) * inner ℝ (S.starProjection e) z + K * a) ^ 2 ≤
      K * L * ((K + L) * V - a ^ 2) := by
  dsimp only
  apply joint_bound_of_two_channels _ _ _ _ _ (‖sourceLoss S r z‖ ^ 2)
  · exact sq_nonneg _
  · rw [← complement_center_norm_sq S r e hr hr0]
    exact sq_nonneg _
  · exact response_sq_le_source_variance S r e z hr hr0
  · exact signed_complement_sq_le S r e z hr hr0 hez

end RiemannResearch.Analysis.CenteredProjectionResponse
