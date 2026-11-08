/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed energy after revealing an orthogonal component

Source: user-provided CanonicalPrimePowerUpdatesResearch20261107, Sections 2,
5 and 7, and the direct Hilbert-space calculation developed in continuation.
This supports the CRT canonical update application in QCRTNestedCutoffs.

The identities retain all signed correlations; no growth bound is assumed.
-/

namespace InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The energy left after removing a genuinely orthogonal component. -/
theorem residual_norm_sq_of_inner_eq (r t : H)
    (hrt : inner ℝ r t = ‖t‖ ^ 2) :
    ‖r - t‖ ^ 2 = ‖r‖ ^ 2 - ‖t‖ ^ 2 := by
  rw [norm_sub_sq_real, hrt]
  ring

/-- Revealed old energy enters the signed norm change negatively. -/
theorem norm_sq_sub_norm_sq_refinement (r s t : H)
    (hrt : inner ℝ r t = ‖t‖ ^ 2) :
    ‖s‖ ^ 2 - ‖r‖ ^ 2 =
      -‖t‖ ^ 2 + ‖s - (r - t)‖ ^ 2 +
        2 * inner ℝ (r - t) (s - (r - t)) := by
  have hq := residual_norm_sq_of_inner_eq r t hrt
  have hs := norm_add_sq_real (r - t) (s - (r - t))
  have hsplit : (r - t) + (s - (r - t)) = s := by abel
  rw [hsplit] at hs
  linarith

/-- When the new residual is orthogonal to the revealed component, the
residual increment splits into revealed old energy and a hidden response. -/
theorem increment_norm_sq_refinement (r s t : H)
    (hrt : inner ℝ r t = ‖t‖ ^ 2) (hst : inner ℝ s t = 0) :
    ‖s - r‖ ^ 2 = ‖t‖ ^ 2 + ‖s - (r - t)‖ ^ 2 := by
  have hzt : inner ℝ (s - (r - t)) t = 0 := by
    rw [inner_sub_left, inner_sub_left, hst, hrt,
      real_inner_self_eq_norm_sq]
    ring
  have hsplit : s - r = (s - (r - t)) - t := by abel
  rw [hsplit, norm_sub_sq_real, hzt]
  ring

/-- The signed cross term contains the full negative revealed old energy. -/
theorem correlation_refinement (r s t : H)
    (hrt : inner ℝ r t = ‖t‖ ^ 2) (hst : inner ℝ s t = 0) :
    inner ℝ r (s - r) =
      inner ℝ (r - t) (s - (r - t)) - ‖t‖ ^ 2 := by
  have htr : inner ℝ t r = ‖t‖ ^ 2 := by
    calc
      inner ℝ t r = inner ℝ r t := real_inner_comm r t
      _ = _ := hrt
  have hts : inner ℝ t s = 0 := by
    calc
      inner ℝ t s = inner ℝ s t := real_inner_comm s t
      _ = _ := hst
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
    hrt, htr, hts]
  ring

end InnerProductSpace
