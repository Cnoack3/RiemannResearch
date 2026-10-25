/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Removing directions orthogonal to the tested residual

Source: the user's shrinking-head and coupled-response handoff, 25 October 2026,
and the elementary orthogonal-projection refinement developed in its continuation.
These exact norm subtractions preserve the signed pairing. They do not provide
a uniform arithmetic bound.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.OrthogonalKernelScreening
open RiemannResearch.LinearAlgebra

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem rankOne_norm_sq (u v : E) (_hv : ‖v‖ ^ 2 ≠ 0) :
    ‖u - (inner ℝ u v / ‖v‖ ^ 2) • v‖ ^ 2 =
      ‖u‖ ^ 2 - (inner ℝ u v) ^ 2 / ‖v‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right]
  field_simp
  ring

theorem pairing_sq_le_rankOne (r u v : E) (hr : inner ℝ r v = 0)
    (hv : ‖v‖ ^ 2 ≠ 0) :
    (inner ℝ r u) ^ 2 ≤ ‖r‖ ^ 2 *
      (‖u‖ ^ 2 - (inner ℝ u v) ^ 2 / ‖v‖ ^ 2) := by
  have hp : inner ℝ r (u - (inner ℝ u v / ‖v‖ ^ 2) • v) = inner ℝ r u := by
    rw [inner_sub_right, real_inner_smul_right, hr, mul_zero, sub_zero]
  have h := abs_real_inner_le_norm r (u - (inner ℝ u v / ‖v‖ ^ 2) • v)
  have hh := mul_le_mul h h (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [← pow_two, sq_abs, mul_pow, hp, rankOne_norm_sq u v hv] using hh
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]
theorem pairing_sq_le_finite (r u : E) (z : ι → E) (c : ι → ℝ)
    (hr : ∀ i, inner ℝ r (z i) = 0)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) u) :
    (inner ℝ r u) ^ 2 ≤ ‖r‖ ^ 2 *
      (‖u‖ ^ 2 - ∑ i, c i * inner ℝ (z i) u) := by
  have hp : inner ℝ r (finiteSchurResidual u z c) = inner ℝ r u := by
    simp [finiteSchurResidual, finiteSchurCombination, inner_sub_right,
      inner_sum, real_inner_smul_right, hr]
  have h := abs_real_inner_le_norm r (finiteSchurResidual u z c)
  have hh := mul_le_mul h h (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [← pow_two, sq_abs, mul_pow, hp, finiteSchurResidual_norm_sq u z c hc] using hh
end
end RiemannResearch.Analysis.OrthogonalKernelScreening
