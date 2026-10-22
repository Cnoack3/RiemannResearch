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
# Two Polar Modes

Adapted from the user-provided archive `combined_audited_lean_sources.zip`,
which describes these declarations as extracted from
`combined_audited_manuscript(4).pdf`. The manuscript itself was not bundled
with this continuation, so this module records archive provenance rather than
claiming page-level source verification.
-/

namespace RiemannResearch.RH.CombinedAudited

/-- Every negative direction is detected by the two-polar-mode block once the
base block is nonnegative. -/
theorem two_polar_mode_reduction
    (base m11 m12 m22 x y : ℝ)
    (hbase : 0 ≤ base)
    (hneg : base + (m11 * x ^ 2 + 2 * m12 * x * y + m22 * y ^ 2) < 0) :
    m11 * x ^ 2 + 2 * m12 * x * y + m22 * y ^ 2 < 0 := by
  linarith

/-- Completion of the square for the two-by-two polar quadratic form. -/
theorem two_by_two_complete_square
    (a b c x y : ℝ) (ha : a ≠ 0) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 =
      a * (x + (b / a) * y) ^ 2 +
        ((a * c - b ^ 2) / a) * y ^ 2 := by
  field_simp [ha]
  ring

/-- With positive first diagonal entry, the two-by-two form has a negative
direction exactly when its determinant is negative. This discharges the finite
matrix-sign part of agenda item C2, once the actual reduced entries are
identified. -/
theorem two_by_two_has_negative_direction_iff
    (a b c : ℝ) (ha : 0 < a) :
    (∃ x y : ℝ, a * x ^ 2 + 2 * b * x * y + c * y ^ 2 < 0) ↔
      a * c - b ^ 2 < 0 := by
  constructor
  · rintro ⟨x, y, hneg⟩
    by_contra hdet
    have hdet' : 0 ≤ a * c - b ^ 2 := le_of_not_gt hdet
    rw [two_by_two_complete_square a b c x y (ne_of_gt ha)] at hneg
    have h1 : 0 ≤ a * (x + (b / a) * y) ^ 2 :=
      mul_nonneg (le_of_lt ha) (sq_nonneg _)
    have h2 : 0 ≤ ((a * c - b ^ 2) / a) * y ^ 2 :=
      mul_nonneg (div_nonneg hdet' (le_of_lt ha)) (sq_nonneg _)
    linarith
  · intro hdet
    refine ⟨-(b / a), 1, ?_⟩
    rw [two_by_two_complete_square a b c (-(b / a)) 1 (ne_of_gt ha)]
    have hquot : (a * c - b ^ 2) / a < 0 :=
      div_neg_of_neg_of_pos hdet ha
    simpa using hquot

end RiemannResearch.RH.CombinedAudited
