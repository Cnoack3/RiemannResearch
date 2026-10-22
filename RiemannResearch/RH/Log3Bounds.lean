/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact rational enclosures for `Real.log 3`

This module specializes Mathlib's finite odd-power-series bounds for
`log ((1 + x) / (1 - x))` at `x = 1 / 2`. The specialization gives
kernel-checked rational bounds for `Real.log 3`; no decimal approximation is
introduced as an assumption.
-/

namespace RiemannResearch.RH.Log3Bounds

open scoped BigOperators

/-- The first `n` terms of the odd-power series for
`(1 / 2) * log ((1 + x) / (1 - x))`, specialized at `x = 1 / 2`. -/
noncomputable def logThreePartialSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)

/-- Every finite specialized odd-power sum is a lower bound for
`(1 / 2) * Real.log 3`. -/
theorem two_mul_logThreePartialSum_le_log_three (n : ℕ) :
    2 * logThreePartialSum n ≤ Real.log 3 := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) n
  norm_num [logThreePartialSum] at h ⊢
  linarith

/-- The geometric tail estimate from Mathlib gives a rational upper bound for
`Real.log 3` at every truncation depth. -/
theorem log_three_le_two_mul_logThreePartialSum_add_remainder (n : ℕ) :
    Real.log 3 ≤
      2 * (logThreePartialSum n + (1 / 2 : ℝ) ^ (2 * n + 1) / (3 / 4)) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) n
  norm_num [logThreePartialSum] at h ⊢
  linarith

/-- A 15-decimal exact rational enclosure for `Real.log 3`, proved from 27
terms of the odd-power series and its rigorous tail bound. -/
theorem log_three_interval_15 :
    (1098612288668109 / 1000000000000000 : ℝ) < Real.log 3 ∧
      Real.log 3 < (1098612288668110 / 1000000000000000 : ℝ) := by
  constructor
  · have h := Real.sum_range_le_log_div
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 27
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  · have h := Real.log_div_le_sum_range_add
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 27
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith

end RiemannResearch.RH.Log3Bounds
