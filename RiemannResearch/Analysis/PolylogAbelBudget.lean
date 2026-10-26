/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.Analysis.LogSquareTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite logarithmic Abel budget
Source: discrete summation by parts in the user's squarefree CRT research agenda.
The profile-increment estimate and the complete summable budget are unconditional.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.LogTailWeights
open RiemannResearch.Analysis

/-- A denominator-monotonicity bound for one discrete profile increment. -/
theorem polylogTailProfile_succ_sub_le (k t : ℕ) :
    polylogTailProfile k (t + 1) - polylogTailProfile k t ≤
      1 / ((k : ℝ) + 6 + Real.log ((t + 1 : ℕ) : ℝ)) ^ k := by
  by_cases ht : t = 0
  · simp [ht, polylogTailProfile_eq]
  have htpos : 0 < t := Nat.pos_of_ne_zero ht
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast htpos
  have hlog : Real.log (t : ℝ) ≤ Real.log ((t + 1 : ℕ) : ℝ) :=
    Real.log_le_log htR (by exact_mod_cast Nat.le_succ t)
  have hd : 0 < (k : ℝ) + 6 + Real.log (t : ℝ) := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith [Real.log_nonneg ht1]
  have hpow : ((k : ℝ) + 6 + Real.log (t : ℝ)) ^ k ≤
      ((k : ℝ) + 6 + Real.log ((t + 1 : ℕ) : ℝ)) ^ k :=
    pow_le_pow_left₀ hd.le (by linarith) k
  have hfrac : (t : ℝ) / ((k : ℝ) + 6 + Real.log ((t + 1 : ℕ) : ℝ)) ^ k ≤
      (t : ℝ) / ((k : ℝ) + 6 + Real.log (t : ℝ)) ^ k :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg t) (pow_pos hd k) hpow
  calc
    _ = ((t : ℝ) / ((k : ℝ) + 6 + Real.log ((t + 1 : ℕ) : ℝ)) ^ k -
        (t : ℝ) / ((k : ℝ) + 6 + Real.log (t : ℝ)) ^ k) +
        1 / ((k : ℝ) + 6 + Real.log ((t + 1 : ℕ) : ℝ)) ^ k := by
      rw [polylogTailProfile_eq, polylogTailProfile_eq]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ _ := by linarith

/-- The reciprocal envelope produces a summable logarithmic-square majorant. -/
theorem polylogTwo_increment_div_succ_le (t : ℕ) :
    (polylogTailProfile 2 (t + 1) - polylogTailProfile 2 t) / ((t : ℝ) + 1) ≤
      1 / (((t : ℝ) + 1) * (6 + Real.log ((t : ℝ) + 1)) ^ 2) := by
  have hdif := polylogTailProfile_succ_sub_le 2 t
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hdif
  have ht : 0 < (t : ℝ) + 1 := by positivity
  have hlog : 0 ≤ Real.log ((t : ℝ) + 1) :=
    Real.log_nonneg (by have hn := Nat.cast_nonneg (α := ℝ) t; linarith)
  have h6 : 0 < 6 + Real.log ((t : ℝ) + 1) := by linarith
  have h8 : 0 < 8 + Real.log ((t : ℝ) + 1) := by linarith
  have hrecip : 1 / (8 + Real.log ((t : ℝ) + 1)) ^ 2 ≤
      1 / (6 + Real.log ((t : ℝ) + 1)) ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos h6)
    nlinarith
  calc
    _ ≤ (1 / (8 + Real.log ((t : ℝ) + 1)) ^ 2) / ((t : ℝ) + 1) :=
      div_le_div_of_nonneg_right hdif ht.le
    _ ≤ (1 / (6 + Real.log ((t : ℝ) + 1)) ^ 2) / ((t : ℝ) + 1) :=
      div_le_div_of_nonneg_right hrecip ht.le
    _ = _ := by
      field_simp [ne_of_gt ht, ne_of_gt h6]

/-- The universal finite budget used by reciprocal cumulative-moment bounds. -/
def reciprocalCrossBudget : ℝ :=
  ∑' n : ℕ, 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)

theorem reciprocalCrossBudget_nonneg : 0 ≤ reciprocalCrossBudget := by
  apply tsum_nonneg
  intro n
  positivity

theorem reciprocalCrossBudget_le_third : reciprocalCrossBudget ≤ (1 : ℝ) / 3 := by
  have hs : Summable (fun n : ℕ =>
      1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)) := by
    simpa only [Real.rpow_two] using summable_shifted_log_square
  have he : reciprocalCrossBudget =
      ∑' k : ℕ, 1 / (((k + 1 : ℕ) : ℝ) *
        (6 + Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) := by
    simpa [reciprocalCrossBudget] using hs.tsum_eq_zero_add
  rw [he]
  have hb := log_power_tail_square (M := 1) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_neg_one] at hb ⊢
  exact hb

end RiemannResearch.Analysis.LogTailWeights
