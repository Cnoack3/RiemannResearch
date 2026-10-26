/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete tails of the centered reciprocal multiplier

Source: direct multiplier comparison for signed regularity localization.
-/

noncomputable section
namespace RiemannResearch.RH.QShiftedReciprocal
open ZetaTwoHilbert QAnnihilatorTailEscape QFiniteSupportDualCriterion

/-- On the complete physical tail m ≥ n+1, centering B at 1/(n+2)
has operator bound 1/(n+2). No finite-tail approximation is used. -/
theorem centered_upperTail_energy_le (f : QHilbert) (n : ℕ) :
    ‖tail n (B f - (1 / ((n : ℝ) + 2)) • f)‖ ^ 2 ≤
      (1 / ((n : ℝ) + 2)) ^ 2 * ‖f‖ ^ 2 := by
  have hsq : ‖tail n (B f - (1 / ((n : ℝ) + 2)) • f)‖ ^ 2 ≤
      ‖(1 / ((n : ℝ) + 2)) • f‖ ^ 2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
      (qCoordinate_square_summable _)
    intro i
    change ((B f - (1 / ((n : ℝ) + 2)) • f) i -
      finiteHead n (B f - (1 / ((n : ℝ) + 2)) • f) i) ^ 2 ≤
      ((1 / ((n : ℝ) + 2)) * f i) ^ 2
    by_cases hi : n ≤ i
    · rw [finiteHead_apply_eq_zero _ _ _ hi, sub_zero]
      change (f i / ((i : ℝ) + 2) -
        (1 / ((n : ℝ) + 2)) * f i) ^ 2 ≤
          ((1 / ((n : ℝ) + 2)) * f i) ^ 2
      have hd : 0 < (n : ℝ) + 2 := by positivity
      have hid : 0 < (i : ℝ) + 2 := by positivity
      have hlo : 0 ≤ 1 / ((i : ℝ) + 2) := by positivity
      have hni : (n : ℝ) + 2 ≤ (i : ℝ) + 2 := by
        have hni' : (n : ℝ) ≤ i := by exact_mod_cast hi
        linarith
      have hhi : 1 / ((i : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
        one_div_le_one_div_of_le hd hni
      have ha : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
      have hc : (1 / ((i : ℝ) + 2) - 1 / ((n : ℝ) + 2)) ^ 2 ≤
          (1 / ((n : ℝ) + 2)) ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (f i))
      convert hm using 1 <;> ring
    · rw [finiteHead_apply_of_lt _ _ _ (by omega), sub_self]
      simpa only [zero_pow (by decide : 2 ≠ 0)] using
        sq_nonneg ((1 / ((n : ℝ) + 2)) * f i)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 / ((n : ℝ) + 2)), mul_pow] at hsq
  exact hsq

/-- An interval bound for any scalar centering on a complete physical tail. -/
theorem centered_tail_energy_le_of_interval (f : QHilbert) (H : ℕ) (a c : ℝ)
    (hc : 0 ≤ c) (ha : a ≤ c)
    (hupper : 1 / ((H : ℝ) + 2) ≤ a + c) :
    ‖tail H (B f - a • f)‖ ^ 2 ≤ c ^ 2 * ‖f‖ ^ 2 := by
  have hsq : ‖tail H (B f - a • f)‖ ^ 2 ≤ ‖c • f‖ ^ 2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
      (qCoordinate_square_summable _)
    intro i
    change ((B f - a • f) i - finiteHead H (B f - a • f) i) ^ 2 ≤
      (c * f i) ^ 2
    by_cases hi : H ≤ i
    · rw [finiteHead_apply_eq_zero _ _ _ hi, sub_zero]
      change (f i / ((i : ℝ) + 2) - a * f i) ^ 2 ≤ (c * f i) ^ 2
      have hHd : 0 < (H : ℝ) + 2 := by positivity
      have hlo : 0 ≤ 1 / ((i : ℝ) + 2) := by positivity
      have hHi : (H : ℝ) + 2 ≤ (i : ℝ) + 2 := by
        have hh : (H : ℝ) ≤ i := by exact_mod_cast hi
        linarith
      have hhi : 1 / ((i : ℝ) + 2) ≤ a + c :=
        (one_div_le_one_div_of_le hHd hHi).trans hupper
      have hleft : 0 ≤ c - (1 / ((i : ℝ) + 2) - a) := by linarith
      have hright : 0 ≤ c + (1 / ((i : ℝ) + 2) - a) := by linarith
      have hm : (1 / ((i : ℝ) + 2) - a) ^ 2 ≤ c ^ 2 := by
        nlinarith [mul_nonneg hleft hright]
      have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg (f i))
      convert hm' using 1 <;> ring
    · rw [finiteHead_apply_of_lt _ _ _ (by omega), sub_self]
      simpa only [zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (c * f i)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_pow] at hsq
  exact hsq

/-- Keep the original evaluation-site center, but permit a cutoff below that site.
The complete tail remains controlled whenever the two sites have bounded ratio. -/
theorem centered_relativeTail_energy_le (f : QHilbert) (n H : ℕ) (C : ℝ)
    (hC : 1 ≤ C) (hscale : (n : ℝ) + 2 ≤ (C + 1) * ((H : ℝ) + 2)) :
    ‖tail H (B f - (1 / ((n : ℝ) + 2)) • f)‖ ^ 2 ≤
      (C / ((n : ℝ) + 2)) ^ 2 * ‖f‖ ^ 2 := by
  have hn : 0 < (n : ℝ) + 2 := by positivity
  have hH : 0 < (H : ℝ) + 2 := by positivity
  apply centered_tail_energy_le_of_interval
  · exact div_nonneg (by linarith) hn.le
  · exact div_le_div_of_nonneg_right hC hn.le
  · rw [← add_div]
    apply (div_le_div_iff₀ hH hn).2
    nlinarith [hscale]

/-- The midpoint of the tail multiplier interval minimizes the uniform multiplier
bound. It improves the energy constant by four, with a changed head response. -/
theorem midpoint_tail_energy_le (f : QHilbert) (H : ℕ) :
    ‖tail H (B f - (1 / (2 * ((H : ℝ) + 2))) • f)‖ ^ 2 ≤
      (1 / (2 * ((H : ℝ) + 2))) ^ 2 * ‖f‖ ^ 2 := by
  apply centered_tail_energy_le_of_interval
  · positivity
  · exact le_rfl
  · have hH : (H : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
    apply le_of_eq
    field_simp
    ring

open scoped BigOperators

/-- The complete raw-source tail has a quadratic gain at every cutoff. -/
theorem reciprocal_tail_energy_le (f : QHilbert) (H : ℕ) :
    ‖tail H (B f)‖ ^ 2 ≤ ‖f‖ ^ 2 / ((H : ℝ) + 2) ^ 2 := by
  have h := centered_tail_energy_le_of_interval f H 0
    (1 / ((H : ℝ) + 2)) (by positivity) (by positivity) (by simp)
  simpa only [zero_smul, sub_zero, one_div, inv_pow, div_eq_mul_inv, one_mul, mul_comm] using h

/-- The complete nonnegative deficit after isolating physical sites one and two. -/
def B_twoCoordinate_tailDefect (f : QHilbert) : ℝ :=
  ∑' n : ℕ, ((1 / 4 : ℝ) - 1 / ((n : ℝ) + 4)) * (f (n + 2)) ^ 2

private theorem B_twoCoordinate_tailDefect_term (f : QHilbert) (n : ℕ) :
    ((1 / 4 : ℝ) - 1 / ((n : ℝ) + 4)) * (f (n + 2)) ^ 2 =
      (f (n + 2)) ^ 2 / 4 - (f (n + 2)) ^ 2 / (((n + 2 : ℕ) : ℝ) + 2) := by
  push_cast
  ring

theorem B_twoCoordinate_tailDefect_summable (f : QHilbert) :
    Summable (fun n : ℕ =>
      ((1 / 4 : ℝ) - 1 / ((n : ℝ) + 4)) * (f (n + 2)) ^ 2) := by
  have hs := (summable_nat_add_iff 2).mpr (qCoordinate_square_summable f)
  have hsB : Summable (fun n : ℕ => (f n) ^ 2 / ((n : ℝ) + 2)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _
      (qCoordinate_square_summable f)
    intro n
    apply div_le_self (sq_nonneg _)
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hb := (summable_nat_add_iff 2).mpr hsB
  apply ((hs.div_const 4).sub hb).congr
  intro n
  exact (B_twoCoordinate_tailDefect_term f n).symm

theorem B_twoCoordinate_tailDefect_nonneg (f : QHilbert) :
    0 ≤ B_twoCoordinate_tailDefect f := by
  apply tsum_nonneg
  intro n
  apply mul_nonneg _ (sq_nonneg _)
  apply sub_nonneg.mpr
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

/-- Exact complete-tail decomposition before any nonnegative remainder is dropped. -/
theorem B_inner_two_coordinate_exact (f : QHilbert) :
    inner ℝ f (B f) = ‖f‖ ^ 2 / 4 + (f 0) ^ 2 / 4 + (f 1) ^ 2 / 12 -
      B_twoCoordinate_tailDefect f := by
  have hs := qCoordinate_square_summable f
  have hsB : Summable (fun n : ℕ => (f n) ^ 2 / ((n : ℝ) + 2)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
    intro n
    apply div_le_self (sq_nonneg _)
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hsTail : Summable (fun n : ℕ => (f (n + 2)) ^ 2) :=
    (summable_nat_add_iff 2).mpr hs
  have hsBTail : Summable (fun n : ℕ =>
      (f (n + 2)) ^ 2 / (((n + 2 : ℕ) : ℝ) + 2)) :=
    (summable_nat_add_iff 2).mpr hsB
  have hd : B_twoCoordinate_tailDefect f =
      (∑' n : ℕ, (f (n + 2)) ^ 2) / 4 -
        ∑' n : ℕ, (f (n + 2)) ^ 2 / (((n + 2 : ℕ) : ℝ) + 2) := by
    unfold B_twoCoordinate_tailDefect
    simp_rw [B_twoCoordinate_tailDefect_term]
    rw [(hsTail.div_const 4).tsum_sub hsBTail, tsum_div_const]
  have hf := hs.sum_add_tsum_nat_add 2
  have hb := hsB.sum_add_tsum_nat_add 2
  rw [← qNorm_sq] at hf
  rw [← B_inner_tsum] at hb
  norm_num [Finset.sum_range_succ] at hf hb
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hd
  linarith

/-- The inequality discards only the named nonnegative complete tail. -/
theorem B_inner_le_two_coordinate_split (f : QHilbert) :
    inner ℝ f (B f) ≤ ‖f‖ ^ 2 / 4 + (f 0) ^ 2 / 4 + (f 1) ^ 2 / 12 := by
  have he := B_inner_two_coordinate_exact f
  have hn := B_twoCoordinate_tailDefect_nonneg f
  linarith


end RiemannResearch.RH.QShiftedReciprocal
