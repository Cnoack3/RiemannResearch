/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith

/-!
# Normalized weighted heads under energy convergence

Source: the user-provided squarefree moving-head argument, 26 October 2026.
These are general dominated-convergence estimates for nonnegative summable
energies. The concrete consumer is the actual squarefree Q correction.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis

/-- A growing monotone weight, normalized at the head endpoint, kills the
weighted head of any fixed nonnegative summable sequence. -/
theorem normalized_weighted_head_tendsto_zero
    (a e : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (ha_mono : Monotone a)
    (ha_top : Tendsto a atTop atTop)
    (he : ∀ n, 0 ≤ e n) (he_sum : Summable e) :
    Tendsto (fun H : ℕ =>
      (∑ n ∈ Finset.range (H + 1), a n * e n) / a H)
      atTop (𝓝 0) := by
  classical
  let f : ℕ → ℕ → ℝ := fun H n =>
    if n ≤ H then a n * e n / a H else 0
  have hf_nonneg (H n : ℕ) : 0 ≤ f H n := by
    dsimp [f]
    split_ifs with hn
    · exact div_nonneg (mul_nonneg (ha n) (he n)) (ha H)
    · exact le_rfl
  have hf_bound (H n : ℕ) : ‖f H n‖ ≤ e n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg H n)]
    by_cases hn : n ≤ H
    · dsimp [f]
      rw [if_pos hn]
      by_cases hzero : a H = 0
      · simpa only [hzero, div_zero] using he n
      · have hpos : 0 < a H := lt_of_le_of_ne (ha H) (Ne.symm hzero)
        apply (div_le_iff₀ hpos).2
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right (ha_mono hn) (he n)
    · simpa only [f, if_neg hn] using he n
  have hf_limit (n : ℕ) :
      Tendsto (fun H : ℕ => f H n) atTop (𝓝 0) := by
    have hc : Tendsto (fun H : ℕ => a n * e n / a H) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ha_top
    apply hc.congr'
    filter_upwards [eventually_ge_atTop n] with H hH
    simp only [f, if_pos hH]
  have htsum : Tendsto (fun H : ℕ => ∑' n : ℕ, f H n) atTop (𝓝 0) := by
    simpa only [tsum_zero] using
      (tendsto_tsum_of_dominated_convergence
        (f := f) (g := fun _ : ℕ => (0 : ℝ)) he_sum hf_limit
        (Eventually.of_forall hf_bound))
  have hfinite (H : ℕ) :
      (∑' n : ℕ, f H n) =
        (∑ n ∈ Finset.range (H + 1), a n * e n) / a H := by
    calc
      (∑' n : ℕ, f H n) = ∑ n ∈ Finset.range (H + 1), f H n := by
        apply tsum_eq_sum
        intro n hn
        have hnot : ¬ n ≤ H := by
          simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
        simp only [f, if_neg hnot]
      _ = ∑ n ∈ Finset.range (H + 1), a n * e n / a H := by
        apply Finset.sum_congr rfl
        intro n hn
        have hle : n ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
        simp only [f, if_pos hle]
      _ = (∑ n ∈ Finset.range (H + 1), a n * e n) / a H := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
  simpa only [hfinite] using htsum

/-- Normalizing a finite weighted head by its endpoint profile bounds it
by the complete unweighted energy. -/
theorem normalized_weighted_head_le_tsum
    (a e : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hmono : Monotone a)
    (he : ∀ n, 0 ≤ e n) (hs : Summable e) (H : ℕ) :
    (∑ n ∈ Finset.range (H + 1), a n * e n) / a H ≤ ∑' n, e n := by
  by_cases hz : a H = 0
  · simpa only [hz, div_zero] using tsum_nonneg he
  have hp : 0 < a H := lt_of_le_of_ne (ha H) (Ne.symm hz)
  apply (div_le_iff₀ hp).2
  calc
    (∑ n ∈ Finset.range (H + 1), a n * e n)
        ≤ ∑ n ∈ Finset.range (H + 1), a H * e n := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (hmono (Nat.le_of_lt_succ (Finset.mem_range.mp hn))) (he n)
    _ = a H * ∑ n ∈ Finset.range (H + 1), e n := by rw [Finset.mul_sum]
    _ ≤ a H * ∑' n, e n :=
      mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum (Finset.range (H + 1)) (fun n _ => he n)) (ha H)
    _ = (∑' n, e n) * a H := mul_comm _ _

/-- A convergent sequence of nonnegative energies in l1 has sub-profile
growth on every divergent finite head. No weighted summability is assumed. -/
theorem normalized_weighted_head_tendsto_zero_of_l1
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hmono : Monotone a)
    (hatop : Tendsto a atTop atTop)
    (u : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    (hu : ∀ j n, 0 ≤ u j n) (hv : ∀ n, 0 ≤ v n) (hs : Summable v)
    (hd : ∀ j, Summable (fun n => |u j n - v n|))
    (hlim : Tendsto (fun j => ∑' n, |u j n - v n|) atTop (𝓝 0))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun j =>
      (∑ n ∈ Finset.range (H j + 1), a n * u j n) / a (H j))
      atTop (𝓝 0) := by
  have hfixed : Tendsto (fun j =>
      (∑ n ∈ Finset.range (H j + 1), a n * v n) / a (H j))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (normalized_weighted_head_tendsto_zero a v ha hmono hatop hv hs).comp hH
  have hbound (j : ℕ) :
      (∑ n ∈ Finset.range (H j + 1), a n * u j n) / a (H j) ≤
      (∑' n, |u j n - v n|) +
        (∑ n ∈ Finset.range (H j + 1), a n * v n) / a (H j) := by
    have hsum : (∑ n ∈ Finset.range (H j + 1), a n * u j n) ≤
        (∑ n ∈ Finset.range (H j + 1), a n * |u j n - v n|) +
          (∑ n ∈ Finset.range (H j + 1), a n * v n) := by
      calc
        _ ≤ ∑ n ∈ Finset.range (H j + 1), a n * (|u j n - v n| + v n) := by
          apply Finset.sum_le_sum
          intro n hn
          apply mul_le_mul_of_nonneg_left _ (ha n)
          linarith [le_abs_self (u j n - v n)]
        _ = _ := by simp_rw [mul_add]; rw [Finset.sum_add_distrib]
    have hdiv := div_le_div_of_nonneg_right hsum (ha (H j))
    rw [add_div] at hdiv
    exact hdiv.trans (add_le_add
      (normalized_weighted_head_le_tsum a (fun n => |u j n - v n|)
        ha hmono (fun n => abs_nonneg _) (hd j) (H j)) le_rfl)
  exact squeeze_zero
    (fun j => div_nonneg
      (Finset.sum_nonneg (fun n _ => mul_nonneg (ha n) (hu j n))) (ha (H j)))
    hbound (by simpa using hlim.add hfixed)

end RiemannResearch.Analysis
