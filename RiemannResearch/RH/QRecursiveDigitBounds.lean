/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QMixedRadixCarry
import Mathlib.Analysis.PSeries

/-! # Physical bounds for the quotient digit in a prime recursion

The estimates hold for any positive radix, including a repeated prime.
The eighth moment uses the full inverse-square measure on integer sites. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.CRTCarryArithmetic
open ArithmeticCumulative

/-- The normalized digit supplied when extending a denominator from D to Dp. -/
def quotientDigit (D p n : ℕ) : ℝ := (((n / D) % p : ℕ) : ℝ) / (p : ℝ)

theorem quotientDigit_nonneg (D p n : ℕ) : 0 ≤ quotientDigit D p n := by
  unfold quotientDigit
  positivity

theorem quotientDigit_eq_zero_of_lt (D p n : ℕ) (hn : n < D) :
    quotientDigit D p n = 0 := by
  simp [quotientDigit, Nat.div_eq_of_lt hn]

theorem residueFraction_eq_parent_add_digit (D p n : ℕ) (hD : 0 < D) (hp : 0 < p) :
    residueFraction (D * p) n = residueFraction D n / (p : ℝ) + quotientDigit D p n := by
  rw [residueFraction_product_digit D p n hD hp, add_div, quotientDigit]

theorem quotientDigit_le_residueFraction (D p n : ℕ) (hD : 0 < D) (hp : 0 < p) :
    quotientDigit D p n ≤ residueFraction (D * p) n := by
  rw [residueFraction_eq_parent_add_digit D p n hD hp]
  have h : 0 ≤ residueFraction D n / (p : ℝ) := by
    unfold residueFraction
    positivity
  linarith

theorem quotientDigit_le_min (D p n : ℕ) (hD : 0 < D) (hp : 0 < p) :
    quotientDigit D p n ≤ min 1 ((n : ℝ) / ((D * p : ℕ) : ℝ)) := by
  have ht := Nat.mul_pos hD hp
  apply (quotientDigit_le_residueFraction D p n hD hp).trans
  change ((n % (D * p) : ℕ) : ℝ) / ((D * p : ℕ) : ℝ) ≤ _
  apply le_min
  · rw [div_le_iff₀ (by exact_mod_cast ht), one_mul]
    exact_mod_cast (Nat.mod_lt n ht).le
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.mod_le n (D * p)

/-- A single new digit has total inverse-square eighth moment at most 3/(Dp). -/
theorem quotientDigit_eighth_moment (D p : ℕ) (hD : 0 < D) (hp : 0 < p) :
    (∑' n : ℕ, quotientDigit D p n ^ 8 / (n : ℝ)^2) ≤ 3 / ((D * p : ℕ) : ℝ) := by
  let T := D * p
  have hT : 0 < T := Nat.mul_pos hD hp
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  let f := fun n : ℕ => quotientDigit D p n ^ 8 / (n : ℝ)^2
  have hmin (n : ℕ) := quotientDigit_le_min D p n hD hp
  have ha (n : ℕ) : quotientDigit D p n ≤ 1 := (hmin n).trans (min_le_left _ _)
  have hb (n : ℕ) : quotientDigit D p n ≤ (n : ℝ) / (T : ℝ) :=
    (hmin n).trans (min_le_right _ _)
  have hi (n : ℕ) : f n ≤ 1 / (n : ℝ)^2 :=
    div_le_div_of_nonneg_right (pow_le_one₀ (quotientDigit_nonneg _ _ _) (ha n)) (sq_nonneg _)
  have hc (n : ℕ) : f n ≤ 1 / (T : ℝ)^2 := by
    by_cases hn : n = 0
    · subst n
      simp [f]
      <;> positivity
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hs : quotientDigit D p n ^ 8 ≤ quotientDigit D p n ^ 2 := by
      calc
        _ = quotientDigit D p n ^ 2 * quotientDigit D p n ^ 6 := by ring
        _ ≤ quotientDigit D p n ^ 2 * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (quotientDigit_nonneg _ _ _) (ha n)) (sq_nonneg _)
        _ = _ := mul_one _
    calc
      f n ≤ ((n : ℝ) / (T : ℝ))^2 / (n : ℝ)^2 :=
        div_le_div_of_nonneg_right (hs.trans (pow_le_pow_left₀
          (quotientDigit_nonneg _ _ _) (hb n) 2)) (sq_nonneg _)
      _ = _ := by field_simp [hnR.ne', hTR.ne']
  have hf : Summable f := Summable.of_nonneg_of_le (fun n => by dsimp [f]; positivity) hi
    (Real.summable_one_div_nat_pow.mpr (by norm_num))
  have ht (N : ℕ) : (∑ k ∈ Finset.range N, f (k + (T+1))) ≤
      1 / (T : ℝ) - 1 / ((N : ℝ) + (T : ℝ)) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hx : 0 < (N : ℝ) + (T : ℝ) := by positivity
      have hstep : f (N + (T+1)) ≤
          1 / ((N : ℝ) + (T : ℝ)) - 1 / ((N : ℝ) + (T : ℝ) + 1) := by
        apply (hi _).trans
        push_cast
        rw [show (N : ℝ) + ((T : ℝ) + 1) = (N : ℝ) + (T : ℝ) + 1 by ring]
        generalize (N : ℝ) + (T : ℝ) = x at hx ⊢
        have hx1 : 0 < x + 1 := by positivity
        field_simp [hx.ne', hx1.ne']
        <;> nlinarith
      push_cast
      rw [show (N:ℝ)+1+(T:ℝ) = (N:ℝ)+(T:ℝ)+1 by ring]
      linarith only [ih, hstep]
  have htail : (∑' k : ℕ, f (k + (T+1))) ≤ 1 / (T : ℝ) := by
    apply le_of_tendsto (((summable_nat_add_iff (T+1)).mpr hf).hasSum.tendsto_sum_nat)
    exact Eventually.of_forall fun N => (ht N).trans (sub_le_self _ (by positivity))
  have hhead : (∑ k ∈ Finset.range (T+1), f k) ≤ ((T : ℝ)+1) / (T : ℝ)^2 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (T+1), 1 / (T : ℝ)^2 :=
        Finset.sum_le_sum (fun k _ => hc k)
      _ = _ := by simp [div_eq_mul_inv]
  change (∑' n, f n) ≤ 3 / (T : ℝ)
  rw [← hf.sum_add_tsum_nat_add (T+1)]
  apply (add_le_add hhead htail).trans
  have hTR1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  field_simp [hTR.ne']
  <;> nlinarith

end RiemannResearch.RH.CRTCarryArithmetic
