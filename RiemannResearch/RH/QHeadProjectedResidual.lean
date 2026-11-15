/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHeadResidualCompletion
import RiemannResearch.Analysis.DenseProjectionTesting
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Projected residual denominators for exact coordinate-head repairs

Source: user-provided reciprocal-head investigation, 7 November 2026,
Section 6. These are exact finite-head identities and division-free bounds.
The projected residual head can be smaller than the complete residual tail;
its norm is not replaced by an arithmetic rate.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QFiniteSupportDualCriterion
open ZetaTwoHilbert
open RiemannResearch.Analysis.DenseProjectionTesting

theorem matching_head_finiteHead_eq (N : ℕ) (x F : QHilbert)
    (hh : ∀ n < N, F n = x n) : finiteHead N F = finiteHead N x := by
  unfold finiteHead
  apply Finset.sum_congr rfl
  intro n hn
  rw [hh n (Finset.mem_range.mp hn)]

/-- The complete repair tail is an orthogonal component of the repair. -/
theorem matching_head_tail_norm_le (N : ℕ) (x F : QHilbert)
    (hh : ∀ n < N, F n = x n) : ‖F - finiteHead N x‖ ≤ ‖F‖ := by
  have hsplit := finiteHead_norm_sq_split N F
  rw [matching_head_finiteHead_eq N x F hh] at hsplit
  nlinarith [sq_nonneg ‖finiteHead N x‖, norm_nonneg (F - finiteHead N x),
    norm_nonneg F]

/-- Division-free bound by the complete repair norm, valid at a zero tail. -/
theorem matching_head_complete_pairing_bound (N : ℕ) (x F r : QHilbert)
    (ho : inner ℝ r F = 0)
    (hh : ∀ n < N, F n = x n) :
    |inner ℝ r (finiteHead N x)| ≤ ‖F‖ * ‖r - finiteHead N r‖ :=
  (matching_head_pairing_bound N x F r ho hh).trans
    (mul_le_mul_of_nonneg_right (matching_head_tail_norm_le N x F hh)
      (norm_nonneg _))

variable (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]

/-- Legality transfers the head pairing to the projection of the residual head. -/
theorem matching_head_projected_pairing (N : ℕ) (x F r : QHilbert)
    (hF : F ∈ S) (hh : ∀ n < N, F n = x n) :
    inner ℝ r (finiteHead N x) =
      inner ℝ F (S.starProjection (finiteHead N r)) := by
  rw [← inner_eq_projected_test S hF (finiteHead N r),
    inner_finiteHead_eq_sum, inner_finiteHead_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hh n (Finset.mem_range.mp hn)]
  ring

/-- The strongest denominator obtained by projecting the finite residual test. -/
theorem matching_head_projected_pairing_bound (N : ℕ) (x F r : QHilbert)
    (hF : F ∈ S) (hh : ∀ n < N, F n = x n) :
    |inner ℝ r (finiteHead N x)| ≤
      ‖F‖ * ‖S.starProjection (finiteHead N r)‖ := by
  rw [matching_head_projected_pairing S N x F r hF hh]
  exact abs_real_inner_le_norm _ _

/-- Orthogonality identifies the projected head with minus the projected tail. -/
theorem projected_residual_head_eq_neg_tail (N : ℕ) (r : QHilbert)
    (hr : r ∈ Sᗮ) :
    S.starProjection (finiteHead N r) =
      -S.starProjection (r - finiteHead N r) := by
  have hz : S.starProjection r = 0 :=
    S.starProjection_apply_eq_zero_iff.mpr hr
  rw [map_sub, hz, zero_sub, neg_neg]

/-- The projected-head denominator is no larger than the actual residual tail. -/
theorem projected_residual_head_norm_le (N : ℕ) (r : QHilbert)
    (hr : r ∈ Sᗮ) :
    ‖S.starProjection (finiteHead N r)‖ ≤ ‖r - finiteHead N r‖ := by
  rw [projected_residual_head_eq_neg_tail S N r hr, norm_neg]
  exact S.norm_starProjection_apply_le _

end RiemannResearch.RH.QFiniteSupportDualCriterion
