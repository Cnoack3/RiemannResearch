/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.NormNum

/-!
# Weighted absolute-sum contraction under aggregation by frequency

Source: the user's prime-torus Plancherel question (2026-10-28),
Mathlib finite-torus Fourier theory, and the cited project modules.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis

theorem weighted_fiber_sum_bound {κ Γ : Type*}
    (a : κ → ℂ) (mode : κ → Γ) (w : Γ → ℝ)
    (hw : ∀ n, 1 ≤ w n)
    (ha : Summable (fun i => ‖a i‖ * w (mode i))) :
    Summable (fun n => ‖∑' i : (mode ⁻¹' ({n} : Set Γ)), a i‖ * w n) ∧
      (∑' n, ‖∑' i : (mode ⁻¹' ({n} : Set Γ)), a i‖ * w n) ≤
        ∑' i, ‖a i‖ * w (mode i) := by
  classical
  let B : Γ → ℝ := fun n => ∑' i : (mode ⁻¹' ({n} : Set Γ)), ‖a i‖ * w (mode i)
  have hB : HasSum B (∑' i, ‖a i‖ * w (mode i)) := by
    exact ha.hasSum.tsum_fiberwise mode
  have ha0 : Summable (fun i => ‖a i‖) := by
    apply ha.of_norm_bounded
    intro i
    rw [norm_norm]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hw (mode i)) (norm_nonneg (a i))
  have hrow (n : Γ) : ‖∑' i : (mode ⁻¹' ({n} : Set Γ)), a i‖ * w n ≤ B n := by
    calc
      _ ≤ (∑' i : (mode ⁻¹' ({n} : Set Γ)), ‖a i‖) * w n :=
        mul_le_mul_of_nonneg_right
          (norm_tsum_le_tsum_norm (ha0.subtype (fun i => i ∈ mode ⁻¹' ({n} : Set Γ))))
          ((by norm_num : (0:ℝ) ≤ 1).trans (hw n))
      _ = B n := by
        rw [← tsum_mul_right]
        dsimp only [B]
        apply tsum_congr
        intro i
        have hi : mode i = n := by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using i.property
        rw [hi]
  have hs : Summable (fun n => ‖∑' i : (mode ⁻¹' ({n} : Set Γ)), a i‖ * w n) := by
    apply hB.summable.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
      ((by norm_num : (0:ℝ) ≤ 1).trans (hw n)))]
    exact hrow n
  exact ⟨hs, (Summable.tsum_le_tsum hrow hs hB.summable).trans_eq hB.tsum_eq⟩

end RiemannResearch.Analysis
