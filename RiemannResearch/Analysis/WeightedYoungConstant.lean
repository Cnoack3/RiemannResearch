/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Optimal scalar coefficient in a weighted Young comparison

Source: the standard completing-the-square identity for weighted Young's inequality.
The concrete RH consumer is `RH/QSquarefreeShortHeadYoung.lean`, where these lemmas
optimize the comparison of the actual signed short-head block energy with the
complete-tail remainder. They do not supply the arithmetic short-head bound.
-/

namespace RiemannResearch.Analysis.WeightedYoungConstant

/-- The exact gap from the optimal scalar coefficient is a square. -/
theorem young_constant_gap_exact (C Z t : ℝ)
    (hC : 0 ≤ C) (hZ : 0 ≤ Z) (ht : t ≠ 0) :
    ((1 + t) * C + 4 * Z * (1 + 1 / t)) - (Real.sqrt C + 2 * Real.sqrt Z) ^ 2 =
      (t * Real.sqrt C - 2 * Real.sqrt Z) ^ 2 / t := by
  let a := Real.sqrt C
  let b := Real.sqrt Z
  have hCa : a ^ 2 = C := Real.sq_sqrt hC
  have hZb : b ^ 2 = Z := Real.sq_sqrt hZ
  change ((1 + t) * C + 4 * Z * (1 + 1 / t)) - (a + 2 * b) ^ 2 = (t * a - 2 * b) ^ 2 / t
  rw [← hCa, ← hZb]
  field_simp [ht] <;> ring

theorem young_constant_ge_optimum (C Z t : ℝ)
    (hC : 0 ≤ C) (hZ : 0 ≤ Z) (ht : 0 < t) :
    (Real.sqrt C + 2 * Real.sqrt Z) ^ 2 ≤ (1 + t) * C + 4 * Z * (1 + 1 / t) := by
  have he := young_constant_gap_exact C Z t hC hZ ht.ne'
  have hp := div_nonneg (sq_nonneg (t * Real.sqrt C - 2 * Real.sqrt Z)) ht.le
  linarith

/-- The explicit optimal positive parameter for the scalar comparison.
This optimizes a proved upper bound; it does not prove the arithmetic source bound. -/
theorem young_constant_at_optimal_parameter (C Z : ℝ) (hC : 0 < C) (hZ : 0 < Z) :
    (1 + (2 * Real.sqrt Z / Real.sqrt C)) * C +
      4 * Z * (1 + 1 / (2 * Real.sqrt Z / Real.sqrt C)) =
        (Real.sqrt C + 2 * Real.sqrt Z) ^ 2 := by
  let a := Real.sqrt C
  let b := Real.sqrt Z
  have ha : 0 < a := Real.sqrt_pos.mpr hC
  have hb : 0 < b := Real.sqrt_pos.mpr hZ
  have hCa : a ^ 2 = C := Real.sq_sqrt hC.le
  have hZb : b ^ 2 = Z := Real.sq_sqrt hZ.le
  change (1 + 2 * b / a) * C + 4 * Z * (1 + 1 / (2 * b / a)) = (a + 2 * b) ^ 2
  rw [← hCa, ← hZb]
  field_simp [ha.ne', hb.ne'] <;> ring


end RiemannResearch.Analysis.WeightedYoungConstant
