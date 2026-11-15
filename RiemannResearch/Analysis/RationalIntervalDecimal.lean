/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RationalInterval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Positivity

/-! Outward decimal rounding preserves certified real enclosures. -/

namespace RiemannResearch.RatInterval

/-- A finite rational certificate can be rounded to a common decimal grid
without making an assumption about the enclosed real number. -/
def decimalHull (digits : ℕ) (I : RatInterval) : RatInterval :=
  let scale : ℚ := 10 ^ digits
  ⟨(⌊I.lo * scale⌋ : ℚ) / scale,
   (⌈I.hi * scale⌉ : ℚ) / scale⟩

theorem contains_decimalHull {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (digits : ℕ) : (decimalHull digits I).Contains x := by
  have hs : (0 : ℚ) < 10 ^ digits := by positivity
  apply contains_weaken hx
  · change (⌊I.lo * (10 : ℚ) ^ digits⌋ : ℚ) / 10 ^ digits ≤ I.lo
    apply (div_le_iff₀ hs).mpr
    exact Int.floor_le _
  · change I.hi ≤ (⌈I.hi * (10 : ℚ) ^ digits⌉ : ℚ) / 10 ^ digits
    apply (le_div_iff₀ hs).mpr
    exact Int.le_ceil _

end RiemannResearch.RatInterval
