/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Scalar Counterterm

Adapted from the user-provided archive `combined_audited_lean_sources.zip`,
which describes these declarations as extracted from
`combined_audited_manuscript(4).pdf`. The manuscript itself was not bundled
with this continuation, so this module records archive provenance rather than
claiming page-level source verification.
-/

namespace RiemannResearch.RH.CombinedAudited

/-- The canonical scalar negative-part counterterm. -/
def scalarNegativePart (x : ℝ) : ℝ := max (-x) 0

/-- Adding the negative part makes a scalar cutoff nonnegative. -/
theorem add_scalarNegativePart_nonnegative (x : ℝ) :
    0 ≤ x + scalarNegativePart x := by
  by_cases hx : 0 ≤ x
  · simp [scalarNegativePart, hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hneg : 0 ≤ -x := neg_nonneg.mpr hx'
    rw [scalarNegativePart, max_eq_left hneg]
    linarith

/-- The canonical counterterm vanishes exactly when no negative scalar mode exists. -/
theorem scalarNegativePart_eq_zero_iff (x : ℝ) :
    scalarNegativePart x = 0 ↔ 0 ≤ x := by
  constructor
  · intro h
    by_contra hx
    have hpos : 0 < -x := neg_pos.mpr (lt_of_not_ge hx)
    have hle : -x ≤ scalarNegativePart x := le_max_left _ _
    rw [h] at hle
    linarith
  · intro hx
    simp [scalarNegativePart, max_eq_right (neg_nonpos.mpr hx)]

end RiemannResearch.RH.CombinedAudited
