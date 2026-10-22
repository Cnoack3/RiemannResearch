/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import RiemannResearch.Analysis.InverseSquareAbelTail
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite rational certificates with complete inverse-square tails.
Source: QLatticeRegularizationResearch20261018.md, period-210 certificate.
The tail estimates reuse the project's elementary telescoping bounds.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFiniteEnergyBounds
open ZetaTwoProbability ZetaTwoHilbert
open RiemannResearch.Analysis.InverseSquareAbelTail

theorem zetaTwo_split (K : ℕ) :
    zetaTwo = (∑ n ∈ Finset.range K, 1 / (n + 1 : ℝ)^2) +
      ∑' n, weight K n := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : zetaTwo = ∑' n : ℕ, 1 / (n + 1 : ℝ)^2 := by
    rw [zetaTwo_eq_nat_sum, hs.tsum_eq_zero_add]
    norm_num
  rw [hshift]
  have h := ((summable_nat_add_iff 1).mpr hs).sum_add_tsum_nat_add K
  simpa only [weight, Nat.cast_add, Nat.cast_one, add_assoc] using h.symm

set_option maxRecDepth 100000 in
theorem zetaTwo_rational_bounds :
    (1028 : ℝ)/625 < zetaTwo ∧ zetaTwo < 329/200 := by
  have hlo := weight_mass_lower 100
  have hhi := weight_mass_upper 100 (by norm_num)
  have he := zetaTwo_split 100
  have hrat :
      (1028 : ℚ)/625 < (∑ n ∈ Finset.range 100, 1 / (n + 1 : ℚ)^2) + 1/101 ∧
      (∑ n ∈ Finset.range 100, 1 / (n + 1 : ℚ)^2) + 1/100 < 329/200 := by
    decide +kernel
  have hr :
      (1028 : ℝ)/625 < (∑ n ∈ Finset.range 100, 1 / (n + 1 : ℝ)^2) + 1/101 ∧
      (∑ n ∈ Finset.range 100, 1 / (n + 1 : ℝ)^2) + 1/100 < 329/200 := by
    have h1 : (((1028 : ℚ)/625) : ℝ) <
        (((∑ n ∈ Finset.range 100, 1 / (n + 1 : ℚ)^2) + 1/101 : ℚ) : ℝ) := by
      exact_mod_cast hrat.1
    have h2 : (((∑ n ∈ Finset.range 100, 1 / (n + 1 : ℚ)^2) + 1/100 : ℚ) : ℝ) <
        (((329 : ℚ)/200) : ℝ) := by exact_mod_cast hrat.2
    push_cast at h1 h2
    exact ⟨h1, h2⟩
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hlo hhi
  constructor <;> linarith

theorem inverse_zetaTwo_rational_bounds :
    (6079 : ℝ)/10000 < 1/zetaTwo ∧ 1/zetaTwo < 76/125 := by
  obtain ⟨hl, hu⟩ := zetaTwo_rational_bounds
  constructor
  · apply (lt_div_iff₀ zetaTwo_pos).mpr
    nlinarith
  · apply (div_lt_iff₀ zetaTwo_pos).mpr
    nlinarith

theorem norm_sq_unweighted (x : QHilbert) :
    ‖x‖^2 = (1/zetaTwo) *
      ∑' n : ℕ, (qSequence x (n+1))^2 / (n+1 : ℝ)^2 := by
  have hs := SquarefreeRadicalDifference.qNormalized_square_summable x
  simp only [div_pow] at hs
  have hn : ‖x‖^2 = (1/zetaTwo) *
      ∑' n : ℕ, (qSequence x n)^2 / (n : ℝ)^2 := by
    rw [qNorm_weighted_sq, ← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold positiveQWeight
    ring
  rw [hn, hs.tsum_eq_zero_add]
  simp only [qSequence_zero, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add,
    Nat.cast_add, Nat.cast_one]

theorem norm_sq_le_head_tail (x : QHilbert) (K : ℕ) (hK : 0 < K)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ n, |qSequence x n| ≤ B) :
    ‖x‖^2 ≤ (1/zetaTwo) *
      ((∑ n ∈ Finset.range K, (qSequence x (n+1))^2/(n+1 : ℝ)^2) + B^2/K) := by
  have hs := SquarefreeRadicalDifference.qNormalized_square_summable x
  simp only [div_pow] at hs
  have hs' : Summable (fun n : ℕ => (qSequence x (n+1))^2/(n+1 : ℝ)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have ht : (∑' n : ℕ, (qSequence x (n+K+1))^2/(n+K+1 : ℝ)^2) ≤ B^2/K := by
    have hb' (n : ℕ) : (qSequence x (n+K+1))^2 ≤ B^2 :=
      by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb (n+K+1))
    have hsTail : Summable (fun n : ℕ => (qSequence x (n+K+1))^2/(n+K+1 : ℝ)^2) := by
      simpa only [Nat.cast_add] using (summable_nat_add_iff K).mpr hs'
    have hsum := hsTail.tsum_le_tsum
      (fun n => show (qSequence x (n+K+1))^2/(n+K+1 : ℝ)^2 ≤ B^2*weight K n by
        simpa only [weight, Nat.cast_add, Nat.cast_one, mul_one_div] using
          div_le_div_of_nonneg_right (hb' n) (sq_nonneg (n+K+1 : ℝ)))
      ((weight_summable K).mul_left (B^2))
    have hm := mul_le_mul_of_nonneg_left (weight_mass_upper K hK) (sq_nonneg B)
    rw [tsum_mul_left] at hsum
    simpa only [mul_one_div] using hsum.trans hm
  rw [norm_sq_unweighted, ← hs'.sum_add_tsum_nat_add K]
  apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr zetaTwo_pos).le
  have ht' : (∑' n : ℕ, (qSequence x (n+K+1))^2/((n+K : ℕ)+1 : ℝ)^2) ≤ B^2/K := by
    simpa only [Nat.cast_add] using ht
  exact add_le_add le_rfl ht'

/-- Complete, signed, unnormalized inverse-square product is summable. -/
theorem normalized_product_summable (x y : QHilbert) :
    Summable (fun n : ℕ => qSequence x n * qSequence y n / (n : ℝ)^2) := by
  have hs := (qSequence_product_summable x y).mul_left zetaTwo
  apply hs.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [positiveQWeight]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hZ : zetaTwo ≠ 0 := ne_of_gt zetaTwo_pos
    unfold positiveQWeight
    field_simp [hZ, hnR]

/-- Actual Q pairing as the complete signed inverse-square series. -/
theorem inner_unweighted (x y : QHilbert) :
    inner ℝ x y = (1/zetaTwo) *
      ∑' n : ℕ, qSequence x (n+1) * qSequence y (n+1) / (n+1 : ℝ)^2 := by
  have hs := normalized_product_summable x y
  have hn : inner ℝ x y = (1/zetaTwo) *
      ∑' n : ℕ, qSequence x n * qSequence y n / (n : ℝ)^2 := by
    rw [qInner_weighted, ← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold positiveQWeight
    ring
  rw [hn, hs.tsum_eq_zero_add]
  simp only [qSequence_zero, zero_mul, zero_div, zero_add,
    Nat.cast_add, Nat.cast_one]

/-- A signed finite mixed sum plus an absolute bound on the entire tail.
The finite mixed sum is not replaced by its absolute value. -/
theorem inner_le_head_tail (x y : QHilbert) (K : ℕ) (hK : 0 < K)
    (Bx By : ℝ) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hbx : ∀ n, |qSequence x n| ≤ Bx)
    (hby : ∀ n, |qSequence y n| ≤ By) :
    inner ℝ x y ≤ (1/zetaTwo) *
      ((∑ n ∈ Finset.range K,
        qSequence x (n+1) * qSequence y (n+1) / (n+1 : ℝ)^2) + Bx*By/K) := by
  have hs := normalized_product_summable x y
  have hs' : Summable (fun n : ℕ =>
      qSequence x (n+1) * qSequence y (n+1) / (n+1 : ℝ)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have ht : (∑' n : ℕ,
      qSequence x (n+K+1) * qSequence y (n+K+1) / (n+K+1 : ℝ)^2) ≤
      Bx*By/K := by
    have hb' (n : ℕ) :
        qSequence x (n+K+1) * qSequence y (n+K+1) ≤ Bx*By := by
      calc
        qSequence x (n+K+1) * qSequence y (n+K+1) ≤
            |qSequence x (n+K+1) * qSequence y (n+K+1)| := le_abs_self _
        _ = |qSequence x (n+K+1)| * |qSequence y (n+K+1)| := abs_mul _ _
        _ ≤ Bx*By := mul_le_mul (hbx _) (hby _) (abs_nonneg _) hBx
    have hsTail : Summable (fun n : ℕ =>
        qSequence x (n+K+1) * qSequence y (n+K+1) / (n+K+1 : ℝ)^2) := by
      simpa only [Nat.cast_add] using (summable_nat_add_iff K).mpr hs'
    have hsum := hsTail.tsum_le_tsum
      (fun n => show
        qSequence x (n+K+1) * qSequence y (n+K+1) / (n+K+1 : ℝ)^2 ≤
          (Bx*By)*weight K n by
        simpa only [weight, Nat.cast_add, Nat.cast_one, mul_one_div] using
          div_le_div_of_nonneg_right (hb' n) (sq_nonneg (n+K+1 : ℝ)))
      ((weight_summable K).mul_left (Bx*By))
    have hm := mul_le_mul_of_nonneg_left (weight_mass_upper K hK)
      (mul_nonneg hBx hBy)
    rw [tsum_mul_left] at hsum
    simpa only [mul_one_div] using hsum.trans hm
  rw [inner_unweighted, ← hs'.sum_add_tsum_nat_add K]
  apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr zetaTwo_pos).le
  have ht' : (∑' n : ℕ,
      qSequence x (n+K+1) * qSequence y (n+K+1) / ((n+K : ℕ)+1 : ℝ)^2) ≤
      Bx*By/K := by
    simpa only [Nat.cast_add] using ht
  exact add_le_add le_rfl ht'

end RiemannResearch.RH.QFiniteEnergyBounds
