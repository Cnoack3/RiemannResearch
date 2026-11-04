/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeBoundary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.RH.QSquarefreeDisplacementEnergy

/-!
# Squared reciprocal compression with the complete tail

Source: the user's 4 November 2026 operator-algebra paper, Section 4.
The paper's coefficient 53/54 is sharpened to 39/40 using an exact
three-square certificate. All omitted physical sites are retained as
a convergent nonnegative series. These estimates alone do not prove RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeSquaredCompression
open ZetaTwoHilbert QShiftedReciprocal QSquarefreeBoundary
open QSquarefreeDisplacementEnergy ZetaTwoOptimizerStage

/-- The first four normalized coordinates of the gap for T* T = 4 B^2. -/
def squaredHeadGap (lam x y z : ℝ) : ℝ :=
  (lam - 1) * (2 * x + 3 * y - 4 * z) ^ 2 +
    (lam - 4 / 9) * x ^ 2 + (lam - 1 / 4) * y ^ 2 +
      (lam - 4 / 25) * z ^ 2

/-- An exact rational certificate improving the paper's 53/54 constant. -/
theorem squaredHeadGap_sos_39_40 (x y z : ℝ) :
    squaredHeadGap (39 / 40 : ℝ) x y z =
      (31 / 72 : ℝ) * (x - (54 / 155 : ℝ) * y + (72 / 155 : ℝ) * z) ^ 2 +
      (347 / 775 : ℝ) * (y + (573 / 694 : ℝ) * z) ^ 2 +
      (1171 / 69400 : ℝ) * z ^ 2 := by
  unfold squaredHeadGap
  ring

/-- Exact head/tail formula for the squared reciprocal, including every site. -/
theorem squared_gap_head_tail_exact (f : QHilbert) (lam : ℝ)
    (hfour : f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0) :
    lam * ‖f‖ ^ 2 - 4 * ‖B f‖ ^ 2 =
      squaredHeadGap lam (f 1) (f 2) (f 3) +
        ∑' n : ℕ, (lam - 4 / ((n : ℝ) + 6) ^ 2) * (f (n + 4)) ^ 2 := by
  have hs := qCoordinate_square_summable f
  have hsB := qCoordinate_square_summable (B f)
  have hst : Summable (fun n : ℕ => (f (n + 4)) ^ 2) :=
    (summable_nat_add_iff 4).mpr hs
  have hsBt : Summable (fun n : ℕ => (f (n + 4) / ((n : ℝ) + 6)) ^ 2) := by
    have ht := (summable_nat_add_iff 4).mpr hsB
    norm_num [B_apply, Nat.cast_add, add_assoc] at ht ⊢
    exact ht
  have hsplit := hs.sum_add_tsum_nat_add 4
  have hBsplit := hsB.sum_add_tsum_nat_add 4
  rw [← qNorm_sq f] at hsplit
  rw [← qNorm_sq (B f)] at hBsplit
  norm_num [Finset.sum_range_succ, add_assoc] at hsplit
  norm_num [Finset.sum_range_succ, B_apply, Nat.cast_add, add_assoc] at hBsplit
  have htail :
      (∑' n : ℕ, (lam - 4 / ((n : ℝ) + 6) ^ 2) * (f (n + 4)) ^ 2) =
        lam * (∑' n : ℕ, (f (n + 4)) ^ 2) -
          4 * ∑' n : ℕ, (f (n + 4) / ((n : ℝ) + 6)) ^ 2 := by
    calc
      _ = ∑' n : ℕ, (lam * (f (n + 4)) ^ 2 -
          4 * (f (n + 4) / ((n : ℝ) + 6)) ^ 2) := by
        apply tsum_congr
        intro n
        simp only [div_pow]
        ring
      _ = _ := by
        rw [(hst.mul_left lam).tsum_sub (hsBt.mul_left 4),
          tsum_mul_left, tsum_mul_left]
  have hf0 : f 0 = 2 * f 1 + 3 * f 2 - 4 * f 3 := by linarith
  rw [htail, ← hsplit, ← hBsplit, hf0]
  unfold squaredHeadGap
  ring

/-- Every remaining coefficient is nonnegative for lam at least 1/9. -/
theorem squared_tail_nonneg (f : QHilbert) (lam : ℝ)
    (hlam : (1 / 9 : ℝ) ≤ lam) :
    0 ≤ ∑' n : ℕ, (lam - 4 / ((n : ℝ) + 6) ^ 2) * (f (n + 4)) ^ 2 := by
  apply tsum_nonneg
  intro n
  apply mul_nonneg _ (sq_nonneg _)
  have hn := Nat.cast_nonneg (α := ℝ) n
  have hd : (36 : ℝ) ≤ ((n : ℝ) + 6) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
  have hi : (4 : ℝ) / ((n : ℝ) + 6) ^ 2 ≤ (1 / 9 : ℝ) := by
    calc
      _ ≤ (4 : ℝ) / 36 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
      _ = _ := by norm_num
  linarith

/-- Squared compression is uniformly below the ambient norm-one value. -/
theorem four_B_norm_sq_le_four_site_coordinates (f : QHilbert)
    (hfour : f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0) :
    4 * ‖B f‖ ^ 2 ≤ (39 / 40 : ℝ) * ‖f‖ ^ 2 := by
  have he := squared_gap_head_tail_exact f (39 / 40 : ℝ) hfour
  have ht := squared_tail_nonneg f (39 / 40 : ℝ) (by norm_num)
  have hh : 0 ≤ squaredHeadGap (39 / 40 : ℝ) (f 1) (f 2) (f 3) := by
    rw [squaredHeadGap_sos_39_40]
    positivity
  linarith

theorem four_B_norm_sq_le_four_site {f : QHilbert}
    (hf : fourSiteFunctional f = 0) :
    4 * ‖B f‖ ^ 2 ≤ (39 / 40 : ℝ) * ‖f‖ ^ 2 :=
  four_B_norm_sq_le_four_site_coordinates f (fourSite_coordinates hf)

theorem four_B_norm_sq_le_of_mem_closure {f : QHilbert} (hf : f ∈ closure) :
    4 * ‖B f‖ ^ 2 ≤ (39 / 40 : ℝ) * ‖f‖ ^ 2 :=
  four_B_norm_sq_le_four_site (fourSiteFunctional_zero_on_closure hf)

end RiemannResearch.RH.QSquarefreeSquaredCompression
