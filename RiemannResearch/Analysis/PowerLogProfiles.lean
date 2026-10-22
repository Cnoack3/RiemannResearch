/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.WeightedMertensTransfer

/-!
# Monotone shifted power/log profiles

Exact derivative and monotonicity calculations supporting conductor-uniform
truncation. The free logarithmic shift handles all small positive indices.
-/

noncomputable section
open Set

namespace RiemannResearch.Analysis

/-- A shifted logarithm permits monotonicity down to the first integer. -/
def powerLogPrimitive (ε b c x : ℝ) : ℝ :=
  x^ε * (c + Real.log x)^(-b)

def powerLogDerivative (ε b c x : ℝ) : ℝ :=
  x^(ε-1) * (c + Real.log x)^(-b) * (ε - b/(c + Real.log x))

theorem powerLog_shift_pos {c x : ℝ} (hc : 0 < c) (hx : 1 ≤ x) :
    0 < c + Real.log x := by
  linarith [Real.log_nonneg hx]

/-- The derivative formula is valid for arbitrary real exponents. -/
theorem hasDerivAt_powerLogPrimitive {ε b c x : ℝ}
    (hc : 0 < c) (hx : 1 ≤ x) :
    HasDerivAt (powerLogPrimitive ε b c) (powerLogDerivative ε b c x) x := by
  have hx0 : 0 < x := by linarith
  have hL := powerLog_shift_pos hc hx
  have h1 := Real.hasDerivAt_rpow_const (p := ε) (Or.inl hx0.ne')
  have h2 := ((Real.hasDerivAt_log hx0.ne').const_add c).rpow_const
    (p := -b) (Or.inl hL.ne')
  have hraw := h1.mul h2
  change HasDerivAt (powerLogPrimitive ε b c) _ x at hraw
  convert hraw using 1
  dsimp [powerLogDerivative]
  rw [Real.rpow_sub_one hx0.ne', Real.rpow_sub_one hL.ne']
  field_simp [hx0.ne', hL.ne']
  ring

/-- The exact condition needed for positivity of the derivative on `x≥1`.
For positive ε this is equivalent to choosing the shift c at least b/ε. -/
theorem powerLogDerivative_nonneg {ε b c x : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hbc : b ≤ ε*c) (hx : 1 ≤ x) :
    0 ≤ powerLogDerivative ε b c x := by
  have hx0 : 0 < x := by linarith
  have hL := powerLog_shift_pos hc hx
  have hb : b ≤ ε*(c + Real.log x) := by
    calc
      b ≤ ε*c := hbc
      _ ≤ ε*(c + Real.log x) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.log_nonneg hx)) hε
  have hquot : b/(c + Real.log x) ≤ ε := (div_le_iff₀ hL).mpr hb
  unfold powerLogDerivative
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hL.le _))
    (sub_nonneg.mpr hquot)

theorem powerLogPrimitive_monotoneOn {ε b c : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hbc : b ≤ ε*c) :
    MonotoneOn (powerLogPrimitive ε b c) (Set.Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (1 : ℝ))
  · intro x hx
    exact (hasDerivAt_powerLogPrimitive hc hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_powerLogPrimitive hc (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact powerLogDerivative_nonneg hc hε hbc (interior_subset hx)

theorem powerLogPrimitive_eq_div {ε b c x : ℝ}
    (hc : 0 < c) (hx : 1 ≤ x) :
    powerLogPrimitive ε b c x = x^ε/(c + Real.log x)^b := by
  unfold powerLogPrimitive
  rw [Real.rpow_neg (powerLog_shift_pos hc hx).le]
  rfl

theorem powerLogQuotient_monotoneOn {ε b c : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hbc : b ≤ ε*c) :
    MonotoneOn (fun x : ℝ => x^ε/(c + Real.log x)^b) (Set.Ici 1) := by
  intro x hx y hy hxy
  change x^ε/(c + Real.log x)^b ≤ y^ε/(c + Real.log y)^b
  rw [← powerLogPrimitive_eq_div hc hx, ← powerLogPrimitive_eq_div hc hy]
  exact powerLogPrimitive_monotoneOn hc hε hbc hx hy hxy

/-- Zero is set separately so the arithmetic profile is globally monotone.
This handles cutoff prefixes `P(min M t)` without a special positive case. -/
def powerLogNatProfile (ε b c : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 0 else (t : ℝ)^ε/(c + Real.log (t : ℝ))^b

theorem powerLogNatProfile_nonneg {ε b c : ℝ} (hc : 0 < c) (t : ℕ) :
    0 ≤ powerLogNatProfile ε b c t := by
  by_cases ht : t = 0
  · simp [powerLogNatProfile, ht]
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ht
  simp only [powerLogNatProfile, if_neg ht]
  exact div_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (powerLog_shift_pos hc ht1).le _)

theorem powerLogNatProfile_monotone {ε b c : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hbc : b ≤ ε*c) :
    Monotone (powerLogNatProfile ε b c) := by
  intro m n hmn
  by_cases hm : m = 0
  · subst m
    simpa [powerLogNatProfile] using powerLogNatProfile_nonneg (ε := ε) (b := b) hc n
  have hn : n ≠ 0 := by omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  simpa only [powerLogNatProfile, if_neg hm, if_neg hn] using
    powerLogQuotient_monotoneOn hc hε hbc hm1 hn1 hmnR

/-- The density-tail profile decreases on positive indices for the natural
parameter signs. This complements the increasing signed-prefix profile. -/
theorem powerLogTail_antitoneOn {r b c : ℝ}
    (hc : 0 < c) (hr : 0 ≤ r) (hb : 0 ≤ b) :
    AntitoneOn (fun x : ℝ => x^(-r)/(c + Real.log x)^b) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hLx := powerLog_shift_pos hc hx
  have hLy := powerLog_shift_pos hc hy
  have hLxy : c + Real.log x ≤ c + Real.log y := by
    linarith [Real.log_le_log hx0 hxy]
  have hxyp := Real.rpow_le_rpow_of_nonpos hx0 hxy (neg_nonpos.mpr hr)
  have hLpow := Real.rpow_le_rpow hLx.le hLxy hb
  calc
    _ ≤ x^(-r)/(c + Real.log y)^b :=
      div_le_div_of_nonneg_right hxyp (Real.rpow_nonneg hLy.le _)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _)
      (Real.rpow_pos_of_pos hLx _) hLpow

end RiemannResearch.Analysis
