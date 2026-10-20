/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ScreenedCarry
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Actual nested projection gains controlled by finite block scores

Source: independent Hilbert-space derivation for Christian Noack's CRT-carry
research agenda, 19 October 2026. The exact Pythagorean identity precedes the
Cauchy--Schwarz estimate. No independence or inverse Gram matrix is needed,
so empty and redundant blocks are covered. The RH consumer is the complete
literal CRT block in `RH/QCRTCarryGain.lean`. No asymptotic score lower bound
is assumed or proved here.
-/
noncomputable section
namespace RiemannResearch.Analysis.ScreenedCarry
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
private theorem nested_projection_gain (V W : Submodule ℝ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hVW : V ≤ W) (x : H) :
    ‖screen V x‖ ^ 2 - ‖screen W x‖ ^ 2 =
      ‖W.starProjection x - V.starProjection x‖ ^ 2 := by
  have h := ExhaustiveWalk.nested_projection_energy V W hVW x
  change ‖screen V x‖ ^ 2 =
    ‖screen W x‖ ^ 2 + ‖W.starProjection x - V.starProjection x‖ ^ 2 at h
  linarith

theorem screened_score_sq_le_nested_gain (V W : Submodule ℝ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hVW : V ≤ W) (x z : H) (hz : z ∈ W) :
    (inner ℝ (screen V z) (screen V x)) ^ 2 ≤
      ‖screen V z‖ ^ 2 *
        (‖screen V x‖ ^ 2 - ‖screen W x‖ ^ 2) := by
  have hzw : screen V z ∈ W :=
    W.sub_mem hz (hVW (V.starProjection_apply_mem z))
  have ho := Submodule.starProjection_inner_eq_zero x (screen V z) hzw
  change inner ℝ (screen W x) (screen V z) = 0 at ho
  have he : screen V x = screen W x +
      (W.starProjection x - V.starProjection x) := by
    simp only [screen_apply]
    abel
  have hi : inner ℝ (screen V z) (screen V x) =
      inner ℝ (screen V z) (W.starProjection x - V.starProjection x) := by
    have ho' : inner ℝ (screen V z) (screen W x) = 0 := by
      rw [real_inner_comm]
      exact ho
    rw [he, inner_add_right, ho', zero_add]
  rw [hi, nested_projection_gain V W hVW x]
  have h := norm_inner_le_norm (𝕜 := ℝ) (screen V z)
    (W.starProjection x - V.starProjection x)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using hs

theorem block_score_le_trace_mul_gain {ι : Type*} [Fintype ι]
    (V W : Submodule ℝ H) [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hVW : V ≤ W) (x : H) (z : ι → H) (hz : ∀ i, z i ∈ W) :
    (∑ i, (inner ℝ (screen V (z i)) (screen V x)) ^ 2) ≤
      (∑ i, ‖screen V (z i)‖ ^ 2) *
        (‖screen V x‖ ^ 2 - ‖screen W x‖ ^ 2) := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => screened_score_sq_le_nested_gain V W hVW x (z i) (hz i)

theorem block_score_div_bound_le_gain {ι : Type*} [Fintype ι]
    (V W : Submodule ℝ H) [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hVW : V ≤ W) (x : H) (z : ι → H) (hz : ∀ i, z i ∈ W)
    (T : ℝ) (hT : 0 < T) (htrace : (∑ i, ‖screen V (z i)‖ ^ 2) ≤ T) :
    (∑ i, (inner ℝ (screen V (z i)) (screen V x)) ^ 2) / T ≤
      ‖screen V x‖ ^ 2 - ‖screen W x‖ ^ 2 := by
  apply (div_le_iff₀ hT).mpr
  have hg : 0 ≤ ‖screen V x‖ ^ 2 - ‖screen W x‖ ^ 2 := by
    rw [nested_projection_gain V W hVW x]
    positivity
  exact (block_score_le_trace_mul_gain V W hVW x z hz).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right htrace hg)
end RiemannResearch.Analysis.ScreenedCarry
