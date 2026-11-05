/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FirstMomentTails
import RiemannResearch.RH.QSignedTailRigidity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ordinary signed prefix sums control complete weighted signed tails

The variable `n` indexes physical site `n + 1`. The hypothesis takes the
absolute value only after summation of the physical coordinates.
-/
noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- Ordinary prefix through the physical site `n+1`, divided by its square. -/
def inverseSquarePrefix (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (n+1), a j) / ((n : ℝ)+1)^2

/-- Signed Abel transfer; no assumption on absolute first moments of the sites. -/
theorem summable_weighted_signedTails_of_prefix (a : ℕ → ℝ)
    (h : Summable (inverseSquarePrefix a)) :
    Summable (fun n : ℕ => ∑' j : ℕ, a (j+n) / (((j+n : ℕ) : ℝ)+1)^2) := by
  let F := inverseSquarePrefix a
  let G (n : ℕ) : ℝ := (∑ j ∈ Finset.range n, a j) / ((n : ℝ)+1)^2
  let r (n : ℕ) : ℝ := ((n : ℝ)+1)^2 / ((n : ℝ)+2)^2
  let c (n : ℕ) : ℝ := (1-r n)*F n
  let b (n : ℕ) : ℝ := a n / ((n : ℝ)+1)^2
  have hF : Summable F := h
  have hr0 (n : ℕ) : 0 ≤ r n := by dsimp [r]; positivity
  have hrform (n : ℕ) : 1-r n = (2*(n : ℝ)+3) / ((n : ℝ)+2)^2 := by
    have hn : (n : ℝ)+2 ≠ 0 := by positivity
    dsimp [r]
    field_simp [hn]
    ring
  have hrem (n : ℕ) : 0 ≤ 1-r n := by rw [hrform]; positivity
  have hr1 (n : ℕ) : r n ≤ 1 := by linarith [hrem n]
  have hrmul (n : ℕ) : (n : ℝ)*(1-r n) ≤ 2 := by
    have hn : 0 < ((n : ℝ)+2)^2 := by positivity
    rw [hrform, ← mul_div_assoc, div_le_iff₀ hn]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hGF (n : ℕ) : G (n+1) = r n * F n := by
    have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
    have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
    dsimp [G, r, F, inverseSquarePrefix]
    simp only [Nat.cast_add, Nat.cast_one, show (n : ℝ)+1+1 = (n : ℝ)+2 by ring]
    field_simp [hn1, hn2]
  have hG : Summable G := by
    apply (summable_nat_add_iff 1).mp
    apply Summable.of_norm_bounded hF.norm
    intro n
    simp only [hGF, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr0 n)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hr1 n) (abs_nonneg (F n))
  have hc : Summable c := by
    apply Summable.of_norm_bounded hF.norm
    intro n
    simp only [c, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hrem n)]
    have he : 1-r n ≤ 1 := by linarith [hr0 n]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (abs_nonneg (F n))
  have hm : Summable (fun n : ℕ => (n : ℝ)*|c n|) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)) _
      (hF.abs.mul_left 2)
    intro n
    simp only [c, abs_mul, abs_of_nonneg (hrem n), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrmul n) (abs_nonneg (F n))
  have hrec (n : ℕ) : b n = G (n+1)-G n+c n := by
    have hd : b n = F n - G n := by
      dsimp [b, F, inverseSquarePrefix, G]
      rw [Finset.sum_range_succ]
      ring
    rw [hd, hGF]
    dsimp [c]
    ring
  have hident (n : ℕ) :
      (∑' j : ℕ, b (j+n)) = (∑' j : ℕ, c (j+n)) - G n := by
    have hGk : Summable (fun j : ℕ => G (j+n)) := (summable_nat_add_iff n).mpr hG
    have hGkp : Summable (fun j : ℕ => G ((j+n)+1)) := by
      simpa only [Nat.add_assoc] using (summable_nat_add_iff (n+1)).mpr hG
    have hck : Summable (fun j : ℕ => c (j+n)) := (summable_nat_add_iff n).mpr hc
    have hsplit : (∑' j : ℕ, G (j+n)) = G n + ∑' j : ℕ, G ((j+n)+1) := by
      simpa only [Nat.zero_add, Nat.add_right_comm _ 1 n] using hGk.tsum_eq_zero_add
    calc
      _ = ∑' j : ℕ, (G ((j+n)+1)-G (j+n)+c (j+n)) := tsum_congr (fun j => hrec (j+n))
      _ = _ := by rw [(hGkp.sub hGk).tsum_add hck, hGkp.tsum_sub hGk, hsplit]; ring
  exact ((rawTail_summable_of_firstMoment c hc hm).sub hG).congr (fun n => (hident n).symm)

end RiemannResearch.Analysis

namespace RiemannResearch.RH.QSignedTailRigidity
open ZetaTwoHilbert

/-- A condition directly on the ordinary signed partial sums of the physical sequence. -/
theorem anchoredTail_summable_of_signedPhysicalPrefix (u : QHilbert)
    (h : Summable (Analysis.inverseSquarePrefix (fun n : ℕ => qSequence u (n+1)))) :
    Summable (anchoredTail u) := by
  have hr := Analysis.summable_weighted_signedTails_of_prefix _ h
  apply (summable_nat_add_iff 1).mp
  apply (hr.div_const ZetaTwoProbability.zetaTwo).congr
  intro n
  rw [anchoredTail, if_neg (Nat.succ_ne_zero n), signedTail, ← tsum_div_const]
  apply tsum_congr
  intro j
  have hz := ne_of_gt ZetaTwoProbability.zetaTwo_pos
  have hn : (j : ℝ)+((n : ℝ)+1) ≠ 0 := by positivity
  simp only [signedCoefficient, positiveQWeight, Nat.cast_add,
    Nat.cast_one, add_assoc]
  field_simp [hz, hn]

end RiemannResearch.RH.QSignedTailRigidity
