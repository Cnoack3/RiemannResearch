/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact correction in an orthogonal two-vector subspace

Source: LegalSubspaceProjectionObstruction.md, the user's actual-residual
projection-stability research agenda. The identities retain the full signed
source coefficient before any estimate. The Q arithmetic family is a consumer.
-/

noncomputable section
namespace RiemannResearch.Analysis.OrthogonalPairCorrection
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def pairSpace (h u : H) : Submodule ℝ H :=
  Submodule.span ℝ ({h, u} : Set H)

instance pairSpace_finiteDimensional (h u : H) : FiniteDimensional ℝ (pairSpace h u) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_singleton u).insert h)

theorem left_mem_pairSpace (h u : H) : h ∈ pairSpace h u :=
  Submodule.subset_span (by simp)

theorem right_mem_pairSpace (h u : H) : u ∈ pairSpace h u :=
  Submodule.subset_span (by simp)

theorem projection_pair_eq (h u x : H) (hh : h ≠ 0) (hu : u ≠ 0)
    (horth : inner ℝ h u = 0) :
    (pairSpace h u).starProjection x =
      (inner ℝ x h / ‖h‖ ^ 2) • h + (inner ℝ x u / ‖u‖ ^ 2) • u := by
  have hhn : ‖h‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hh)
  have hun : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hu)
  have horth' : inner ℝ u h = 0 := by rw [real_inner_comm]; exact horth
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((pairSpace h u).add_mem
      ((pairSpace h u).smul_mem _ (left_mem_pairSpace h u))
      ((pairSpace h u).smul_mem _ (right_mem_pairSpace h u)))
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [inner_sub_left, inner_add_left, real_inner_smul_left,
          real_inner_smul_left, real_inner_self_eq_norm_sq, horth', mul_zero,
          add_zero, div_mul_cancel₀ _ hhn, sub_self]
      · rw [inner_sub_left, inner_add_left, real_inner_smul_left,
          real_inner_smul_left, real_inner_self_eq_norm_sq, horth, mul_zero,
          zero_add, div_mul_cancel₀ _ hun, sub_self]
  | zero => simp
  | add y z hy hz ihy ihz => rw [inner_add_right, ihy, ihz, add_zero]
  | smul c y hy ih => rw [real_inner_smul_right, ih, mul_zero]

/-- The target residual after adjoining an orthogonal direction. -/
theorem residual_pair_eq (h u j : H) (c : ℝ)
    (hh : h ≠ 0) (hu : u ≠ 0) (horth : inner ℝ h u = 0)
    (hj : inner ℝ j h = 0) :
    (c • h + j) - (pairSpace h u).starProjection (c • h + j) =
      j - (inner ℝ j u / ‖u‖ ^ 2) • u := by
  rw [projection_pair_eq h u (c • h + j) hh hu horth]
  simp only [inner_add_left, real_inner_smul_left, horth, hj,
    mul_zero, zero_add, add_zero, real_inner_self_eq_norm_sq]
  have hhn : ‖h‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hh)
  rw [mul_div_cancel_right₀ c hhn]
  abel

/-- Exact signed coefficient of the actual projected smoothed residual. -/
theorem correction_pair_eq (h u j : H) (c : ℝ) (B : H →L[ℝ] H)
    (hh : h ≠ 0) (hu : u ≠ 0) (horth : inner ℝ h u = 0)
    (hj : inner ℝ j h = 0) :
    (pairSpace h u).starProjection
        (B ((c • h + j) - (pairSpace h u).starProjection (c • h + j))) =
      (inner ℝ (B (j - (inner ℝ j u / ‖u‖ ^ 2) • u)) h / ‖h‖ ^ 2) • h +
      ((inner ℝ u (B j) * ‖u‖ ^ 2 - inner ℝ j u * inner ℝ u (B u)) /
        (‖u‖ ^ 2) ^ 2) • u := by
  rw [residual_pair_eq h u j c hh hu horth hj,
    projection_pair_eq h u _ hh hu horth]
  congr 1
  congr 1
  rw [map_sub, map_smul, inner_sub_left, real_inner_smul_left,
    real_inner_comm (B j) u, real_inner_comm (B u) u]
  have hun : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hu)
  field_simp [hun]

/-- Explicit coefficient estimate used once the actual arithmetic providers
establish the four finite scalar bounds. -/
theorem correction_coefficient_lower (G a D E : ℝ)
    (hG : 25 ≤ G) (hGM : G ≤ 303) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2)
    (hD : 1 / 36 ≤ D) (hE0 : 0 ≤ E) (hE : E ≤ 1) :
    7 / (36 * 303 ^ 2 : ℝ) ≤ (D * G - a * E) / G ^ 2 := by
  have hGp : 0 < G := by linarith
  have hDG : 25 / 36 ≤ D * G := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ D - 1 / 36)
      (by linarith : 0 ≤ G - 25)]
  have haE : a * E ≤ 1 / 2 := by
    nlinarith [mul_nonneg ha0 (by linarith : 0 ≤ 1 - E)]
  have hsq : G ^ 2 ≤ 303 ^ 2 := by nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hGp)).mpr
  nlinarith

end RiemannResearch.Analysis.OrthogonalPairCorrection
