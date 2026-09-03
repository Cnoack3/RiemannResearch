/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar Schur

Adapted from the user-provided archive `combined_audited_lean_sources.zip`,
which describes these declarations as extracted from
`combined_audited_manuscript(4).pdf`. The manuscript itself was not bundled
with this continuation, so this module records archive provenance rather than
claiming page-level source verification.
-/

namespace RiemannResearch.RH.CombinedAudited

/-- Exact completion of the square underlying a scalar Schur complement. -/
theorem scalar_schur_identity (a b c t : ℝ) (ha : a ≠ 0) :
    a * t ^ 2 - 2 * b * t + c =
      a * (t - b / a) ^ 2 + (c - b ^ 2 / a) := by
  field_simp [ha]
  ring

/-- The scalar Schur complement is the minimum of the quadratic objective. -/
theorem scalar_schur_lower_bound (a b c t : ℝ) (ha : 0 < a) :
    c - b ^ 2 / a ≤ a * t ^ 2 - 2 * b * t + c := by
  rw [scalar_schur_identity a b c t (ne_of_gt ha)]
  have hnonneg : 0 ≤ a * (t - b / a) ^ 2 :=
    mul_nonneg (le_of_lt ha) (sq_nonneg (t - b / a))
  linarith

/-- The completed-square equality is attained at `t = b/a`. -/
theorem scalar_schur_minimizer (a b c : ℝ) (ha : a ≠ 0) :
    a * (b / a) ^ 2 - 2 * b * (b / a) + c = c - b ^ 2 / a := by
  rw [scalar_schur_identity a b c (b / a) ha]
  ring

/-- Nonnegativity of the parallel-sum mismatch penalty used in gluing formulas. -/
theorem parallel_sum_mismatch_nonnegative (a b d : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a * b / (a + b)) * d ^ 2 := by
  have hab : 0 < a + b := add_pos ha hb
  exact mul_nonneg
    (div_nonneg (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (le_of_lt hab))
    (sq_nonneg d)

/-- For a positive leading coefficient, equality in the Schur lower bound
occurs only at the normal-equation solution. -/
theorem scalar_schur_eq_iff (a b c t : ℝ) (ha : 0 < a) :
    a * t ^ 2 - 2 * b * t + c = c - b ^ 2 / a ↔ t = b / a := by
  rw [scalar_schur_identity a b c t (ne_of_gt ha)]
  constructor
  · intro h
    have hz : a * (t - b / a) ^ 2 = 0 := by linarith
    have hsq : (t - b / a) ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt ha)
    nlinarith
  · intro ht
    rw [ht]
    ring

end RiemannResearch.RH.CombinedAudited
