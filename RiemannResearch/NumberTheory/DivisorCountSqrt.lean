/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Elementary square-root divisor bound

The involution d ↦ L/d sends every divisor exceeding sqrt(L) to a divisor
at most sqrt(L). Counting the two halves gives τ(L) ≤ 2 sqrt(L).
-/
noncomputable section
namespace RiemannResearch.NumberTheory.DivisorCountSqrt

/-- Count both members of each divisor pair; a square-root divisor may be
counted twice, which is harmless for this upper bound. -/
theorem card_divisors_le_two_nat_sqrt (L : ℕ) :
    L.divisors.card ≤ 2 * Nat.sqrt L := by
  by_cases hL : L = 0
  · simp [hL]
  have hLp : 0 < L := Nat.pos_of_ne_zero hL
  let S : Finset ℕ := Finset.Icc 1 (Nat.sqrt L)
  have hcover : L.divisors ⊆ S ∪ S.image (fun d => L / d) := by
    intro d hdmem
    have hdL := Nat.dvd_of_mem_divisors hdmem
    have hdp := Nat.pos_of_mem_divisors hdmem
    by_cases hdsmall : d ≤ Nat.sqrt L
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hdp, hdsmall⟩))
    let b := L / d
    have hb : 0 < b := Nat.div_pos (Nat.le_of_dvd hLp hdL) hdp
    have he : d * b = L := Nat.mul_div_cancel' hdL
    have hbsmall : b ≤ Nat.sqrt L := by
      by_contra h
      have hdlarge : Nat.sqrt L + 1 ≤ d := by omega
      have hblarge : Nat.sqrt L + 1 ≤ b := by omega
      have hprod := Nat.mul_le_mul hdlarge hblarge
      have hs := Nat.lt_succ_sqrt L
      nlinarith
    have hbd : b ∣ L := ⟨d, by nlinarith [he]⟩
    have he' : b * (L/b) = L := Nat.mul_div_cancel' hbd
    have hback : L/b = d := by nlinarith
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨b, Finset.mem_Icc.mpr ⟨hb, hbsmall⟩, hback⟩))
  calc
    L.divisors.card ≤ (S ∪ S.image (fun d => L/d)).card := Finset.card_le_card hcover
    _ ≤ S.card + (S.image (fun d => L/d)).card := Finset.card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add_left (Finset.card_image_le) _
    _ = 2 * Nat.sqrt L := by simp [S, two_mul]

/-- The real square-root form used in the collocation instability estimate. -/
theorem card_divisors_le_two_sqrt (L : ℕ) :
    (L.divisors.card : ℝ) ≤ 2 * Real.sqrt (L : ℝ) := by
  have hc : (L.divisors.card : ℝ) ≤ 2 * (Nat.sqrt L : ℝ) := by
    exact_mod_cast card_divisors_le_two_nat_sqrt L
  have hs : (Nat.sqrt L : ℝ)^2 ≤ (L : ℝ) := by
    simpa only [pow_two, Nat.cast_mul] using
      (show ((Nat.sqrt L * Nat.sqrt L : ℕ) : ℝ) ≤ (L : ℝ) by
        exact_mod_cast Nat.sqrt_le L)
  have hr := Real.sq_sqrt (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hn := Real.sqrt_nonneg (L : ℝ)
  nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt L)]

end RiemannResearch.NumberTheory.DivisorCountSqrt
