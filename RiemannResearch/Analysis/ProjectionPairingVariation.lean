/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.Analysis.ProjectionTailSummability
import RiemannResearch.Analysis.NestedProjectionPairing
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absolute variation of pairings along nested orthogonal projections

Source: Section 3 of the user's Pareto parity overshoot continuation,
18 October 2026. Finite Cauchy--Schwarz and exact projection-energy telescoping
give the complete two-gap budget. The concrete RH consumer is
RH.ParetoSignedInnovations. No RH or target-membership assumption occurs.
No mathematical novelty claim is made.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ProjectionPairingVariation
open RiemannResearch.Analysis.ProjectionTailSummability
open RiemannResearch.Analysis.NestedProjectionPairing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (W : ℕ → Submodule ℝ H) [∀ n, (W n).HasOrthogonalProjection]
  (hW : Monotone W)

include hW

theorem sum_abs_step_pairing_sq_le (x y : H) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      |inner ℝ ((W (j + 1)).starProjection x - (W j).starProjection x) y|) ^ 2 ≤
      (‖x - (W 0).starProjection x‖ ^ 2 - ‖x - (W J).starProjection x‖ ^ 2) *
      (‖y - (W 0).starProjection y‖ ^ 2 - ‖y - (W J).starProjection y‖ ^ 2) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range J)
    (r := fun j => |inner ℝ
      ((W (j + 1)).starProjection x - (W j).starProjection x) y|)
    (f := fun j => ‖(W (j + 1)).starProjection x - (W j).starProjection x‖ ^ 2)
    (g := fun j => ‖(W (j + 1)).starProjection y - (W j).starProjection y‖ ^ 2)
    (by intro j hj; positivity) (by intro j hj; positivity)
    (by
      intro j hj
      rw [sq_abs]
      exact nested_pairing_sq_le (hW (Nat.le_succ j)) x y)
  simpa only [sum_projection_step_norm_sq W hW] using hcs

theorem sum_abs_step_pairing_le (x y : H) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      |inner ℝ ((W (j + 1)).starProjection x - (W j).starProjection x) y|) ≤
      Real.sqrt (‖x - (W 0).starProjection x‖ ^ 2 -
        ‖x - (W J).starProjection x‖ ^ 2) *
      Real.sqrt (‖y - (W 0).starProjection y‖ ^ 2 -
        ‖y - (W J).starProjection y‖ ^ 2) := by
  have hx : 0 ≤ ‖x - (W 0).starProjection x‖ ^ 2 -
      ‖x - (W J).starProjection x‖ ^ 2 := by
    rw [← sum_projection_step_norm_sq W hW x J]
    positivity
  have hy : 0 ≤ ‖y - (W 0).starProjection y‖ ^ 2 -
      ‖y - (W J).starProjection y‖ ^ 2 := by
    rw [← sum_projection_step_norm_sq W hW y J]
    positivity
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun j hj => abs_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy] using
    sum_abs_step_pairing_sq_le W hW x y J

theorem step_pairing_abs_summable (x y : H) :
    Summable (fun j =>
      |inner ℝ ((W (j + 1)).starProjection x - (W j).starProjection x) y|) := by
  apply summable_of_sum_range_le (c := ‖x - (W 0).starProjection x‖ *
    ‖y - (W 0).starProjection y‖) (fun j => abs_nonneg _)
  intro J
  apply (sum_abs_step_pairing_le W hW x y J).trans
  have hx : Real.sqrt (‖x - (W 0).starProjection x‖ ^ 2 -
      ‖x - (W J).starProjection x‖ ^ 2) ≤ ‖x - (W 0).starProjection x‖ := by
    calc
      _ ≤ Real.sqrt (‖x - (W 0).starProjection x‖ ^ 2) :=
        Real.sqrt_le_sqrt (sub_le_self _ (sq_nonneg _))
      _ = _ := Real.sqrt_sq (norm_nonneg _)
  have hy : Real.sqrt (‖y - (W 0).starProjection y‖ ^ 2 -
      ‖y - (W J).starProjection y‖ ^ 2) ≤ ‖y - (W 0).starProjection y‖ := by
    calc
      _ ≤ Real.sqrt (‖y - (W 0).starProjection y‖ ^ 2) :=
        Real.sqrt_le_sqrt (sub_le_self _ (sq_nonneg _))
      _ = _ := Real.sqrt_sq (norm_nonneg _)
  exact mul_le_mul hx hy (Real.sqrt_nonneg _) (norm_nonneg _)

theorem tsum_abs_step_pairing_le (x y px py : H)
    (hx : Tendsto (fun n => (W n).starProjection x) atTop (𝓝 px))
    (hy : Tendsto (fun n => (W n).starProjection y) atTop (𝓝 py)) :
    (∑' j, |inner ℝ ((W (j + 1)).starProjection x - (W j).starProjection x) y|) ≤
      Real.sqrt (‖x - (W 0).starProjection x‖ ^ 2 - ‖x - px‖ ^ 2) *
      Real.sqrt (‖y - (W 0).starProjection y‖ ^ 2 - ‖y - py‖ ^ 2) := by
  have hs := (step_pairing_abs_summable W hW x y).hasSum.tendsto_sum_nat
  have hxE : Tendsto (fun n => ‖x - (W n).starProjection x‖ ^ 2)
      atTop (𝓝 (‖x - px‖ ^ 2)) :=
    (tendsto_const_nhds.sub hx).norm.pow 2
  have hyE : Tendsto (fun n => ‖y - (W n).starProjection y‖ ^ 2)
      atTop (𝓝 (‖y - py‖ ^ 2)) :=
    (tendsto_const_nhds.sub hy).norm.pow 2
  have hb : Tendsto (fun n =>
      Real.sqrt (‖x - (W 0).starProjection x‖ ^ 2 -
        ‖x - (W n).starProjection x‖ ^ 2) *
      Real.sqrt (‖y - (W 0).starProjection y‖ ^ 2 -
        ‖y - (W n).starProjection y‖ ^ 2)) atTop
      (𝓝 (Real.sqrt (‖x - (W 0).starProjection x‖ ^ 2 - ‖x - px‖ ^ 2) *
        Real.sqrt (‖y - (W 0).starProjection y‖ ^ 2 - ‖y - py‖ ^ 2))) :=
    ((tendsto_const_nhds.sub hxE).sqrt).mul ((tendsto_const_nhds.sub hyE).sqrt)
  exact le_of_tendsto_of_tendsto hs hb
    (Filter.Eventually.of_forall (sum_abs_step_pairing_le W hW x y))

theorem tsum_step_pairing (x y px : H)
    (hx : Tendsto (fun n => (W n).starProjection x) atTop (𝓝 px)) :
    (∑' j, inner ℝ ((W (j + 1)).starProjection x - (W j).starProjection x) y) =
      inner ℝ (px - (W 0).starProjection x) y := by
  have hs : Summable (fun j =>
      inner ℝ ((W (j + 1)).starProjection x - (W j).starProjection x) y) :=
    summable_abs_iff.mp (step_pairing_abs_summable W hW x y)
  have heq (J : ℕ) :
      (∑ j ∈ Finset.range J,
        inner ℝ ((W (j + 1)).starProjection x - (W j).starProjection x) y) =
        inner ℝ ((W J).starProjection x - (W 0).starProjection x) y := by
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [inner_sub_left]
      ring
  have ht : Tendsto (fun J => ∑ j ∈ Finset.range J,
      inner ℝ ((W (j + 1)).starProjection x - (W j).starProjection x) y) atTop
      (𝓝 (inner ℝ (px - (W 0).starProjection x) y)) := by
    simp_rw [heq]
    exact (hx.sub tendsto_const_nhds).inner tendsto_const_nhds
  exact tendsto_nhds_unique hs.hasSum.tendsto_sum_nat ht

end RiemannResearch.Analysis.ProjectionPairingVariation
