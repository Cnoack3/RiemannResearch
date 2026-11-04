/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ArithmeticProgressionSquareSeries
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Elementary complete-normalization bounds for rational Q certificates.
The lower bound keeps thirty positive terms; the upper bound keeps five terms
and bounds the entire remaining tail by telescoping. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.Analysis.ArithmeticProgressionSquareTail

theorem zetaTwo_gt_twenty_nine_eighteenths : (29 / 18 : ℝ) < zetaTwo := by
  rw [zetaTwo_eq_nat_sum]
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hfinite : (29 / 18 : ℝ) <
      ∑ n ∈ Finset.range 31, 1 / (n : ℝ) ^ 2 := by
    norm_num [Finset.sum_range_succ]
  exact hfinite.trans_le (hs.sum_le_tsum (Finset.range 31) (fun _ _ => by positivity))

theorem zetaTwo_lt_five_thirds : zetaTwo < (5 / 3 : ℝ) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have ht : (∑' k : ℕ, 1 / (((k + 6 : ℕ) : ℝ) ^ 2)) ≤ (1 / 5 : ℝ) := by
    calc
      _ = ∑' k : ℕ, 1 / ((5 : ℝ) + ((k + 1 : ℕ) : ℝ) * 1) ^ 2 := by
        apply tsum_congr
        intro k
        have heq : ((k + 6 : ℕ) : ℝ) = (5 : ℝ) + ((k + 1 : ℕ) : ℝ) * 1 := by
          push_cast
          ring
        rw [heq]
      _ ≤ _ := by simpa using complete_tail_bound 5 1 (by norm_num) (by norm_num)
  rw [zetaTwo_eq_nat_sum, ← hs.sum_add_tsum_nat_add 6]
  calc
    _ ≤ (∑ n ∈ Finset.range 6, 1 / (n : ℝ) ^ 2) + 1 / 5 := by linarith only [ht]
    _ < _ := by norm_num [Finset.sum_range_succ]

end RiemannResearch.RH.ZetaTwoProbability
