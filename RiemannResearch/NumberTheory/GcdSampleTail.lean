/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.DivisorEscapeTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Separate arithmetic energy of gcd sampling on the divisor escape set

Source: continuation of the user's CRT collocation handoff, Section 7.
The tail retains the actual gcd value rather than replacing it by n/2.
-/

noncomputable section

open scoped BigOperators

namespace RiemannResearch.NumberTheory.DivisorEscapeTail

/-- Exact sampled power energy on one positive physical coordinate. -/
def sampleTerm (t : ℝ) (L n : ℕ) : ℝ :=
  if n ∣ L then 0 else (Nat.gcd n L : ℝ) ^ (2 - t) / (n : ℝ) ^ 2

/-- The entire sampled tail; the shift excludes only the anchored zero coordinate. -/
def sampleTail (t : ℝ) (L : ℕ) : ℝ := ∑' n : ℕ, sampleTerm t L (n + 1)

theorem sampleTerm_nonneg (t : ℝ) (L n : ℕ) : 0 ≤ sampleTerm t L n := by
  unfold sampleTerm
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)

/-- Proper-divisor geometry supplies a comparison without replacing the sampled
energy by that comparison in the definition. -/
theorem sampleTerm_le_scaled_escape (t : ℝ) (ht2 : t ≤ 2)
    (L n : ℕ) (hn : 0 < n) :
    sampleTerm t L n ≤ (2 : ℝ) ^ (t - 2) * term t L n := by
  by_cases hnL : n ∣ L
  · simp [sampleTerm, term, hnL]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hg := gcd_rpow_le_half L n hn hnL (2 - t) (sub_nonneg.mpr ht2)
    rw [show -(2 - t) = t-2 by ring] at hg
    have hp : (n : ℝ) ^ (2 - t) = (n : ℝ) ^ 2 * (n : ℝ) ^ (-t) := by
      rw [← Real.rpow_two, ← Real.rpow_add hnR] <;> congr 1 <;> ring
    simp only [sampleTerm, term, if_neg hnL]
    calc
      _ ≤ ((2 : ℝ) ^ (t - 2) * (n : ℝ) ^ (2 - t)) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hg (sq_nonneg _)
      _ = _ := by rw [hp] <;> field_simp

theorem sampleTerm_summable (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) (L : ℕ) :
    Summable (fun n : ℕ => sampleTerm t L (n + 1)) :=
  Summable.of_nonneg_of_le (fun n => sampleTerm_nonneg t L (n + 1))
    (fun n => sampleTerm_le_scaled_escape t ht2 L (n + 1) (Nat.succ_pos n))
    ((summable_shifted_term t ht L).mul_left _)

theorem sampleTail_nonneg (t : ℝ) (L : ℕ) : 0 ≤ sampleTail t L :=
  tsum_nonneg (fun n => sampleTerm_nonneg t L (n + 1))

theorem sampleTail_le_scaled_escape (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) (L : ℕ) :
    sampleTail t L ≤ (2 : ℝ) ^ (t - 2) * tail t L := by
  calc
    _ ≤ ∑' n : ℕ, (2 : ℝ) ^ (t - 2) * term t L (n + 1) :=
      Summable.tsum_le_tsum
        (fun n => sampleTerm_le_scaled_escape t ht2 L (n + 1) (Nat.succ_pos n))
        (sampleTerm_summable t ht ht2 L)
        ((summable_shifted_term t ht L).mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_shifted_term t ht L]

/-- The sampled tail is strictly positive at each positive finite cutoff. -/
theorem sampleTail_pos (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (L : ℕ) (hL : 0 < L) : 0 < sampleTail t L := by
  have hnL : ¬ L + 1 ∣ L := by
    intro h
    have := Nat.le_of_dvd hL h
    omega
  have hterm : 0 < sampleTerm t L (L + 1) := by
    rw [sampleTerm, if_neg hnL]
    apply div_pos
    · exact Real.rpow_pos_of_pos
        (by exact_mod_cast Nat.gcd_pos_of_pos_left L (Nat.succ_pos L)) _
    · positivity
  have hle : sampleTerm t L (L + 1) ≤ sampleTail t L := by
    have h := sum_le_hasSum ({L} : Finset ℕ)
      (fun n _ => sampleTerm_nonneg t L (n + 1)) (sampleTerm_summable t ht ht2 L).hasSum
    simpa only [Finset.sum_singleton, sampleTail] using h
  exact hterm.trans_le hle

/-- The full escape tail is strictly positive at a positive finite cutoff. -/
theorem tail_pos (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (L : ℕ) (hL : 0 < L) : 0 < tail t L := by
  have hp := sampleTail_pos t ht ht2 L hL
  have hle := sampleTail_le_scaled_escape t ht ht2 L
  have hq : 0 < (2 : ℝ) ^ (t - 2) := Real.rpow_pos_of_pos (by norm_num) _
  by_contra h
  have hn := mul_nonpos_of_nonneg_of_nonpos hq.le (le_of_not_gt h)
  linarith

end RiemannResearch.NumberTheory.DivisorEscapeTail
