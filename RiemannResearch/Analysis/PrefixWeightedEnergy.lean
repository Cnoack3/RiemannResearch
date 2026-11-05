/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
/-!
# Prefix bounds and complete weighted sums
Source: the user-directed mean-square displacement continuation, 5 November 2026.
The finite summation-by-parts inequality retains its nonnegative deficit term.
The complete weighted bound is obtained only after proving all finite bounds.
Concrete consumer: RH/QMeanSquareDisplacement.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.PrefixWeightedEnergy

theorem weighted_prefix_with_deficit (a w : ℕ → ℝ) (D C : ℝ)
    (hw : Antitone w)
    (hpre : ∀ n, ∑ i ∈ Finset.range n, a i ≤ D + C * (n : ℝ)) (N : ℕ) :
    (∑ i ∈ Finset.range N, a i * w i) +
      (D + C * (N : ℝ)-∑ i ∈ Finset.range N, a i) * w N ≤
      D * w 0 + C * ∑ i ∈ Finset.range N, w i := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hd : 0 ≤ D + C * ((N + 1 : ℕ) : ℝ)-∑ i ∈ Finset.range (N + 1), a i :=
      sub_nonneg.mpr (hpre (N + 1))
    have hh := mul_le_mul_of_nonneg_left (hw (Nat.le_succ N)) hd
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at hh ⊢
    nlinarith

theorem weighted_prefix_le (a w : ℕ → ℝ) (D C : ℝ)
    (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n)
    (hpre : ∀ n, ∑ i ∈ Finset.range n, a i ≤ D + C * (n : ℝ)) (N : ℕ) :
    ∑ i ∈ Finset.range N, a i * w i ≤ D * w 0 + C * ∑ i ∈ Finset.range N, w i := by
  have h := weighted_prefix_with_deficit a w D C hw hpre N
  have hd := mul_nonneg (sub_nonneg.mpr (hpre N)) (hw0 N)
  linarith

theorem weighted_tsum_le (a w : ℕ → ℝ) (D C : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hC : 0 ≤ C) (hw : Antitone w)
    (hw0 : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hpre : ∀ n, ∑ i ∈ Finset.range n, a i ≤ D + C * (n : ℝ)) :
    (∑' n, a n * w n) ≤ D * w 0 + C * ∑' n, w n := by
  apply Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (ha n) (hw0 n))
  intro N
  exact (weighted_prefix_le a w D C hw hw0 hpre N).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum (Finset.range N) (fun n _ => hw0 n)) hC))

end RiemannResearch.Analysis.PrefixWeightedEnergy


namespace RiemannResearch.Analysis.PrefixWeightedEnergy
theorem weighted_prefix_identity (a w : ℕ → ℝ) (D C : ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, a i * w i) +
      (D + C * (N : ℝ)-∑ i ∈ Finset.range N, a i) * w N +
      (∑ i ∈ Finset.range N,
        (D + C * ((i + 1 : ℕ) : ℝ)-∑ k ∈ Finset.range (i + 1), a k) * (w i - w (i + 1))) =
      D * w 0 + C * ∑ i ∈ Finset.range N, w i := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at ih ⊢
    nlinarith
end RiemannResearch.Analysis.PrefixWeightedEnergy
