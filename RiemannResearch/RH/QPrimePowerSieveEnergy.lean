/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.QPrimePowerPrimorial
import RiemannResearch.RH.QPrimePowerSieve
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete-target energy bounds for the prime-power sieve

Source: the user-directed continuation, 20 October 2026. The exact signed
head is retained before the complete target energy replaces the growing
head maximum. Every full norm includes its infinite Q tail.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoHilbert
open QPrimePowerSieve (finite_head_le_norm_sq)
open ZetaTwoHilbert ZetaTwoProbability

/-- Exact signed finite-head accounting against an actual complete target. -/
theorem head_energy_signed_exact (x y : QHilbert) (a : ℝ) (H : ℕ)
    (he : ∀ n ∈ Finset.Icc 1 H, qSequence x n = qSequence y n - a * (n : ℝ)) :
    (∑ n ∈ Finset.Icc 1 H, positiveQWeight n * (qSequence x n) ^ 2) =
      a ^ 2 * (H : ℝ) / zetaTwo -
        (2 * a / zetaTwo) * (∑ n ∈ Finset.Icc 1 H, qSequence y n / (n : ℝ)) +
        (∑ n ∈ Finset.Icc 1 H, positiveQWeight n * (qSequence y n) ^ 2) := by
  have hp (n : ℕ) (hn : n ∈ Finset.Icc 1 H) :
      positiveQWeight n * (qSequence x n) ^ 2 =
        a ^ 2 / zetaTwo - (2 * a / zetaTwo) * (qSequence y n / (n : ℝ)) +
          positiveQWeight n * (qSequence y n) ^ 2 := by
    have hnN : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnN.ne'
    rw [he n hn]
    unfold positiveQWeight
    field_simp [hn0, ne_of_gt zetaTwo_pos]
    ring
  rw [Finset.sum_congr rfl hp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, ← Finset.mul_sum]
  simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- The target-error term is its complete energy, not a growing head maximum. -/
theorem head_norm_lower_complete_target (x y : QHilbert) (a : ℝ) (H : ℕ)
    (he : ∀ n ∈ Finset.Icc 1 H, qSequence x n = qSequence y n - a * (n : ℝ)) :
    a ^ 2 * (H : ℝ) / (2 * zetaTwo) - ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have hp (n : ℕ) (hn : n ∈ Finset.Icc 1 H) :
      a ^ 2 / (2 * zetaTwo) - positiveQWeight n * (qSequence y n) ^ 2 ≤
        positiveQWeight n * (qSequence x n) ^ 2 := by
    have hnN : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnN.ne'
    have hc : positiveQWeight n * (a * (n : ℝ)) ^ 2 / 2 =
        a ^ 2 / (2 * zetaTwo) := by
      unfold positiveQWeight
      field_simp [hn0, ne_of_gt zetaTwo_pos]
    have hs : (a * (n : ℝ)) ^ 2 / 2 - (qSequence y n) ^ 2 ≤
        (qSequence y n - a * (n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (a * (n : ℝ) - 2 * qSequence y n)]
    have hw := mul_le_mul_of_nonneg_left hs (positiveQWeight_nonneg n)
    rw [he n hn]
    nlinarith [hc]
  have hs := Finset.sum_le_sum hp
  rw [Finset.sum_sub_distrib, Finset.sum_const] at hs
  simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hs
  have hx := finite_head_le_norm_sq x H
  have hy := finite_head_le_norm_sq y H
  have hre : (H : ℝ) * (a ^ 2 / (2 * zetaTwo)) =
      a ^ 2 * (H : ℝ) / (2 * zetaTwo) := by ring
  rw [hre] at hs
  linarith

end RiemannResearch.RH.ZetaTwoHilbert

namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability

theorem primePowerTwoVector_norm_lower_complete_target (H : ℕ) (hH : 2 ≤ H) :
    RiemannResearch.Analysis.finitePrimeProduct H ^ 2 * (H : ℝ) / (2 * zetaTwo) -
      ‖PrimePowerTarget.qTarget 2 (by norm_num)‖ ^ 2 ≤ ‖primePowerTwoVector H‖ ^ 2 := by
  apply head_norm_lower_complete_target
  intro n hn
  rw [PrimePowerTarget.qTarget_sequence]
  exact qSequence_primePowerTwoVector_head H n hH (Finset.mem_Icc.mp hn).2

theorem primePowerTwoVector_norm_lower_uniform (H : ℕ) (hH : 2 ≤ H) :
    RiemannResearch.Analysis.finitePrimeProduct H ^ 2 * (H : ℝ) / (2 * zetaTwo) -
      6 / zetaTwo ≤ ‖primePowerTwoVector H‖ ^ 2 := by
  have ht := PrimePowerTarget.qTarget_norm_sq_bound 2 (by norm_num)
  norm_num at ht
  have hb := primePowerTwoVector_norm_lower_complete_target H hH
  linarith

end RiemannResearch.RH.QPrimePowerSieve
