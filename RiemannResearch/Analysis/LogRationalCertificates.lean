/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RationalInterval
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Computable logarithm enclosures for the actual Pareto tail

The positive atanh series is evaluated using rational arithmetic. Its exact
analytic remainder is bounded by a geometric tail. At the review's shifted
starting points, twelve terms are stronger than its alternating 24-term bound.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.LogRationalCertificates
open RiemannResearch RatInterval

def logOnePlusInvInterval (a : ℚ) (N : ℕ) : RatInterval :=
  let r : ℚ := 1 / (2 * a + 1)
  let P : ℚ := ∑ j ∈ Finset.range N, r ^ (2*j+1) / (2*j+1 : ℕ)
  ⟨2 * P, 2 * (P + r ^ (2*N+1) / (1-r^2))⟩

theorem logOnePlusInvInterval_contains (a : ℚ) (ha : 0 < a) (N : ℕ) :
    (logOnePlusInvInterval a N).Contains (Real.log (((a : ℝ)+1)/(a : ℝ))) := by
  have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hd : (0 : ℝ) < 2 * (a : ℝ) + 1 := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / (2 * (a : ℝ) + 1) := by positivity
  have hr1 : (1 : ℝ) / (2 * (a : ℝ) + 1) < 1 := by
    apply (div_lt_one hd).mpr
    linarith
  have hl := Real.sum_range_le_log_div hr0 hr1 N
  have hu := Real.log_div_le_sum_range_add hr0 hr1 N
  have he : (1 + 1 / (2 * (a : ℝ) + 1)) /
      (1 - 1 / (2 * (a : ℝ) + 1)) = ((a : ℝ)+1)/(a : ℝ) := by
    field_simp [ne_of_gt har, ne_of_gt hd]
    <;> ring
  rw [he] at hl hu
  unfold RatInterval.Contains logOnePlusInvInterval
  dsimp only
  push_cast
  constructor <;> linarith

end RiemannResearch.Analysis.LogRationalCertificates
