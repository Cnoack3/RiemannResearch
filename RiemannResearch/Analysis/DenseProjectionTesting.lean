/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Target membership from bounded testing against a dense family

Source: continuation of the user-provided UnitSignalBoundednessAudit20261022.md,
22 October 2026. The proof is standard Hilbert projection and continuity.
No mathematical novelty is asserted. The complete-Q arithmetic consumer is
RH/QFiniteSupportDualCriterion.lean. The uniform bound is not provided here.
-/

noncomputable section
open scoped Topology

namespace RiemannResearch.Analysis.DenseProjectionTesting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (S : Submodule ℝ E) [S.HasOrthogonalProjection]

theorem inner_eq_projected_test {y : E} (hy : y ∈ S) (a : E) :
    inner ℝ y a = inner ℝ y (S.starProjection a) := by
  have hz := Submodule.starProjection_inner_eq_zero a y hy
  rw [inner_sub_left] at hz
  calc
    inner ℝ y a = inner ℝ a y := real_inner_comm _ _
    _ = inner ℝ (S.starProjection a) y := by linarith
    _ = inner ℝ y (S.starProjection a) := real_inner_comm _ _

theorem mem_of_all_test_bound (y : E) (C : ℝ)
    (h : ∀ a : E, |inner ℝ y a| ≤ C * ‖S.starProjection a‖) : y ∈ S := by
  let r := y - S.starProjection y
  have hr : r ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal (K := S) y
  have hpr : S.starProjection r = 0 :=
    (S.starProjection_apply_eq_zero_iff).mpr hr
  have hzero : inner ℝ (S.starProjection y) r = 0 :=
    Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem y) hr
  have hpair : inner ℝ y r = ‖r‖ ^ 2 := by
    have hh : inner ℝ r r = inner ℝ y r := by
      dsimp [r] at *
      rw [inner_sub_left, hzero, sub_zero]
    rw [← real_inner_self_eq_norm_sq, hh]
  have hh := h r
  rw [hpr, norm_zero, mul_zero, hpair, abs_of_nonneg (sq_nonneg _)] at hh
  have hn : ‖r‖ = 0 := by nlinarith [sq_nonneg ‖r‖]
  have heq : y = S.starProjection y := sub_eq_zero.mp (norm_eq_zero.mp hn)
  rw [heq]
  exact S.starProjection_apply_mem y

theorem mem_iff_dense_test_bound (y : E) (D : Set E) (hD : Dense D) :
    y ∈ S ↔ ∃ C : ℝ, ∀ a ∈ D, |inner ℝ y a| ≤ C * ‖S.starProjection a‖ := by
  constructor
  · intro hy
    refine ⟨‖y‖, ?_⟩
    intro a _
    rw [inner_eq_projected_test S hy a]
    exact abs_real_inner_le_norm _ _
  · rintro ⟨C, hC⟩
    apply mem_of_all_test_bound S y C
    have hc : IsClosed {a : E | |inner ℝ y a| ≤ C * ‖S.starProjection a‖} :=
      isClosed_le (continuous_const.inner continuous_id).abs
        (continuous_const.mul S.starProjection.continuous.norm)
    intro a
    exact (closure_minimal hC hc) (hD a)

end RiemannResearch.Analysis.DenseProjectionTesting
