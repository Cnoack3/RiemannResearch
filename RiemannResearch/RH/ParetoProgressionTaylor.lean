/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoProgressionTails
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact Pareto progression tails and their signed Taylor bounds

Source: the user discussion of Pareto/CRT weights, 11 September 2026.
The coefficients agree with the standard digamma expansion in DLMF 5.7.4;
the proofs here use exact reciprocal-product identities and convergent series.

For positive integer representatives the `progressionWeight Q r` below is the
actual residue mass W_Q(r). The first Pareto atom is removed exactly. The
remaining Taylor inequalities are unconditional, and include their signed
remainders. The odd zeta constants are defined by their convergent positive
p-series; the even constants are evaluated by Mathlib's Basel theorems.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The positive p-series; for natural p > 1 this is the usual zeta value. -/
def positivePSeries (p : ℕ) : ℝ := ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ p

theorem positivePSeries_summable (p : ℕ) (hp : 2 ≤ p) :
    Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ p) := by
  have hs : Summable (fun j : ℕ => 1 / (j : ℝ)^p) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  simpa only [Function.comp_def, Nat.cast_succ] using hs.comp_injective Nat.succ_injective

theorem positivePSeries_two : positivePSeries 2 = Real.pi ^ 2 / 6 := by
  have h : (∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2) =
      ∑' j : ℕ, 1 / (j : ℝ) ^ 2 := by
    simpa using hasSum_zeta_two.summable.tsum_eq_zero_add.symm
  exact h.trans hasSum_zeta_two.tsum_eq

theorem positivePSeries_four : positivePSeries 4 = Real.pi ^ 4 / 90 := by
  have h : (∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 4) =
      ∑' j : ℕ, 1 / (j : ℝ) ^ 4 := by
    simpa using hasSum_zeta_four.summable.tsum_eq_zero_add.symm
  exact h.trans hasSum_zeta_four.tsum_eq

private theorem scaled_pSeries_summable (Q p : ℕ) (hp : 2 ≤ p) :
    Summable (fun j : ℕ => 1 / ((Q : ℝ) * ((j : ℝ) + 1)) ^ p) := by
  simpa only [mul_pow, one_div_mul_one_div] using
    (positivePSeries_summable p hp).mul_left (1 / (Q : ℝ) ^ p)

private theorem scaled_pSeries_tsum (Q p : ℕ) :
    (∑' j : ℕ, 1 / ((Q : ℝ) * ((j : ℝ) + 1)) ^ p) =
      positivePSeries p / (Q : ℝ) ^ p := by
  calc
    _ = ∑' j : ℕ, (1 / (Q : ℝ)^p) * (1 / ((j : ℝ)+1)^p) := by
      apply tsum_congr
      intro j
      rw [mul_pow, one_div_mul_one_div]
    _ = (1 / (Q : ℝ)^p) * positivePSeries p := by
      rw [tsum_mul_left]
      rfl
    _ = positivePSeries p / (Q : ℝ)^p := by ring

private theorem progression_tail_atom (Q r j : ℕ) :
    positiveWeight (r + Q + Q * j) =
      1 / (((Q : ℝ) * ((j : ℝ) + 1) + r) *
        ((Q : ℝ) * ((j : ℝ) + 1) + r + 1)) := by
  unfold positiveWeight
  push_cast
  congr 1 <;> ring

/-- Every progression tail is at most the corresponding reciprocal-square
p-series. This bound is uniform in the residue representative. -/
theorem progressionWeight_sub_atom_le_pSeries (Q r : ℕ) (hQ : 0 < Q) :
    progressionWeight Q r - positiveWeight r ≤ positivePSeries 2 / (Q : ℝ)^2 := by
  rw [progressionWeight_split Q r hQ, add_sub_cancel_left]
  unfold progressionWeight
  rw [← scaled_pSeries_tsum Q 2]
  apply Summable.tsum_le_tsum _ (progressionWeight_summable Q (r + Q) hQ)
    (scaled_pSeries_summable Q 2 le_rfl)
  intro j
  rw [progression_tail_atom]
  apply one_div_le_one_div_of_le (by positivity)
  have hA : (0 : ℝ) < (Q : ℝ) * ((j : ℝ)+1) := by positivity
  have hr : (0 : ℝ) ≤ r := by positivity
  nlinarith [mul_nonneg (le_of_lt hA) hr]

/-- The removed tail is strictly positive, for every positive modulus. -/
theorem progressionWeight_sub_atom_pos (Q r : ℕ) (hQ : 0 < Q) :
    0 < progressionWeight Q r - positiveWeight r := by
  rw [progressionWeight_split Q r hQ, add_sub_cancel_left]
  have hp : 0 < positiveWeight (r + Q) := by
    unfold positiveWeight
    have h : 0 < r + Q := by omega
    positivity
  have hle := (progressionWeight_summable Q (r + Q) hQ).sum_le_tsum
    ({0} : Finset ℕ) (fun j _ => positiveWeight_nonneg _)
  have hle' : positiveWeight (r + Q) ≤ progressionWeight Q (r + Q) := by
    simpa [progressionWeight] using hle
  exact hp.trans_le hle'

/-- The uniform, fully explicit head-plus-Basel bound from the discussion. -/
theorem progressionWeight_head_basel_bounds (Q r : ℕ) (hQ : 0 < Q) :
    0 < progressionWeight Q r - positiveWeight r ∧
      progressionWeight Q r - positiveWeight r ≤ Real.pi ^ 2 / (6 * (Q : ℝ)^2) := by
  constructor
  · exact progressionWeight_sub_atom_pos Q r hQ
  · have h := progressionWeight_sub_atom_le_pSeries Q r hQ
    rw [positivePSeries_two] at h
    convert h using 1 <;> ring

/-- The remainder after the first two terms of the inverse-modulus tail
expansion. It is signed: it will be proved strictly positive below. -/
def progressionTaylorRemainder (Q r : ℕ) : ℝ :=
  progressionWeight Q r - positiveWeight r - positivePSeries 2 / (Q : ℝ)^2 +
    (2 * (r : ℝ) + 1) * (positivePSeries 3 / (Q : ℝ)^3)

private theorem inverse_product_remainder_eq (A r : ℝ) (hA : 0 < A) (hr : 0 ≤ r) :
    1 / ((A + r) * (A + r + 1)) - 1 / A^2 + (2*r+1) * (1 / A^3) =
      ((3*r^2 + 3*r + 1)*A + (2*r+1)*r*(r+1)) /
        (A^3 * (A+r) * (A+r+1)) := by
  have hAr : A + r ≠ 0 := by positivity
  have hAr1 : A + r + 1 ≠ 0 := by positivity
  field_simp [ne_of_gt hA, hAr, hAr1]
  <;> ring

private theorem inverse_product_remainder_pos (A r : ℝ) (hA : 0 < A) (hr : 0 ≤ r) :
    0 < 1 / ((A + r) * (A + r + 1)) - 1 / A^2 +
      (2*r+1) * (1 / A^3) := by
  rw [inverse_product_remainder_eq A r hA hr]
  positivity

private theorem inverse_product_remainder_le (A r : ℝ) (hA : 0 < A) (hr : 0 ≤ r) :
    1 / ((A + r) * (A + r + 1)) - 1 / A^2 + (2*r+1) * (1 / A^3) ≤
      (3*r^2+3*r+1) * (1 / A^4) := by
  have hid : (3*r^2+3*r+1) * (1 / A^4) -
      (1 / ((A + r) * (A + r + 1)) - 1 / A^2 + (2*r+1) * (1 / A^3)) =
      ((4*r^3+6*r^2+4*r+1)*A + (3*r^2+3*r+1)*r*(r+1)) /
        (A^4 * (A+r) * (A+r+1)) := by
    have hAr : A + r ≠ 0 := by positivity
    have hAr1 : A + r + 1 ≠ 0 := by positivity
    field_simp [ne_of_gt hA, hAr, hAr1]
    <;> ring
  have hnonneg : 0 ≤ (3*r^2+3*r+1) * (1 / A^4) -
      (1 / ((A + r) * (A + r + 1)) - 1 / A^2 + (2*r+1) * (1 / A^3)) := by
    rw [hid]
    positivity
  linarith

private def progressionTaylorTerm (Q r j : ℕ) : ℝ :=
  positiveWeight (r+Q+Q*j) - 1 / ((Q : ℝ) * ((j : ℝ)+1))^2 +
    (2*(r : ℝ)+1) * (1 / ((Q : ℝ) * ((j : ℝ)+1))^3)

private theorem progressionTaylorTerm_summable (Q r : ℕ) (hQ : 0 < Q) :
    Summable (progressionTaylorTerm Q r) := by
  exact ((progressionWeight_summable Q (r+Q) hQ).sub
    (scaled_pSeries_summable Q 2 le_rfl)).add
    ((scaled_pSeries_summable Q 3 (by omega)).mul_left (2*(r : ℝ)+1))

private theorem progressionTaylorRemainder_eq_tsum (Q r : ℕ) (hQ : 0 < Q) :
    progressionTaylorRemainder Q r = ∑' j, progressionTaylorTerm Q r j := by
  unfold progressionTaylorRemainder progressionTaylorTerm
  rw [Summable.tsum_add
    ((progressionWeight_summable Q (r+Q) hQ).sub (scaled_pSeries_summable Q 2 le_rfl))
    ((scaled_pSeries_summable Q 3 (by omega)).mul_left (2*(r : ℝ)+1))]
  rw [Summable.tsum_sub (progressionWeight_summable Q (r+Q) hQ)
    (scaled_pSeries_summable Q 2 le_rfl), tsum_mul_left]
  rw [scaled_pSeries_tsum, scaled_pSeries_tsum]
  change progressionWeight Q r - positiveWeight r - _ + _ =
    progressionWeight Q (r+Q) - _ + _
  rw [progressionWeight_split Q r hQ]
  ring

/-- Strict positivity and a complete inverse-fourth-power upper remainder.
The constants depending on r are kept explicit; this is not a fixed-r
asymptotic silently applied uniformly across an expanding CRT chart. -/
theorem progressionTaylorRemainder_bounds (Q r : ℕ) (hQ : 0 < Q) :
    0 < progressionTaylorRemainder Q r ∧
      progressionTaylorRemainder Q r ≤
        (3*(r : ℝ)^2+3*r+1) * (positivePSeries 4 / (Q : ℝ)^4) := by
  have hterm (j : ℕ) : 0 < progressionTaylorTerm Q r j := by
    unfold progressionTaylorTerm
    rw [progression_tail_atom]
    exact inverse_product_remainder_pos _ _ (by positivity) (by positivity)
  rw [progressionTaylorRemainder_eq_tsum Q r hQ]
  constructor
  · have hle := (progressionTaylorTerm_summable Q r hQ).sum_le_tsum
      ({0} : Finset ℕ) (fun j _ => le_of_lt (hterm j))
    have hle' : progressionTaylorTerm Q r 0 ≤ ∑' j, progressionTaylorTerm Q r j := by
      simpa using hle
    exact (hterm 0).trans_le hle'
  · rw [← scaled_pSeries_tsum Q 4, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (progressionTaylorTerm_summable Q r hQ)
      ((scaled_pSeries_summable Q 4 (by omega)).mul_left (3*(r : ℝ)^2+3*r+1))
    intro j
    unfold progressionTaylorTerm
    rw [progression_tail_atom]
    exact inverse_product_remainder_le _ _ (by positivity) (by positivity)

/-- Actual W_Q(r): exact first Pareto atom, the Basel correction, the signed
cubic correction, and an explicit positive remainder bounded using ζ(4). -/
theorem progressionWeight_signed_taylor (Q r : ℕ) (hQ : 0 < Q) :
    progressionWeight Q r = positiveWeight r + Real.pi^2 / (6*(Q : ℝ)^2) -
      (2*(r : ℝ)+1) * positivePSeries 3 / (Q : ℝ)^3 +
      progressionTaylorRemainder Q r ∧
    0 < progressionTaylorRemainder Q r ∧
    progressionTaylorRemainder Q r ≤
      (3*(r : ℝ)^2+3*r+1) * Real.pi^4 / (90*(Q : ℝ)^4) := by
  refine ⟨?_, (progressionTaylorRemainder_bounds Q r hQ).1, ?_⟩
  · unfold progressionTaylorRemainder
    rw [positivePSeries_two]
    ring
  · have h := (progressionTaylorRemainder_bounds Q r hQ).2
    rw [positivePSeries_four] at h
    convert h using 1 <;> ring

/-- Positive magnitude of the negative remainder after retaining the
inverse-fourth-power term. -/
def progressionTaylorSecondRemainder (Q r : ℕ) : ℝ :=
  (3*(r : ℝ)^2+3*r+1) * (positivePSeries 4 / (Q : ℝ)^4) -
    progressionTaylorRemainder Q r

private def progressionTaylorSecondTerm (Q r j : ℕ) : ℝ :=
  (3*(r : ℝ)^2+3*r+1) * (1 / ((Q : ℝ)*((j : ℝ)+1))^4) -
    progressionTaylorTerm Q r j

private theorem inverse_product_second_remainder_eq (A r : ℝ) (hA : 0 < A)
    (hr : 0 ≤ r) :
    (3*r^2+3*r+1) * (1 / A^4) -
      (1 / ((A+r)*(A+r+1)) - 1 / A^2 + (2*r+1)*(1 / A^3)) =
      ((4*r^3+6*r^2+4*r+1)*A + (3*r^2+3*r+1)*r*(r+1)) /
        (A^4 * (A+r) * (A+r+1)) := by
  have hAr : A+r ≠ 0 := by positivity
  have hAr1 : A+r+1 ≠ 0 := by positivity
  field_simp [ne_of_gt hA, hAr, hAr1]
  <;> ring

private theorem inverse_product_second_remainder_pos (A r : ℝ) (hA : 0 < A)
    (hr : 0 ≤ r) :
    0 < (3*r^2+3*r+1) * (1 / A^4) -
      (1 / ((A+r)*(A+r+1)) - 1 / A^2 + (2*r+1)*(1 / A^3)) := by
  rw [inverse_product_second_remainder_eq A r hA hr]
  positivity

private theorem inverse_product_second_remainder_le (A r : ℝ) (hA : 0 < A)
    (hr : 0 ≤ r) :
    (3*r^2+3*r+1) * (1 / A^4) -
      (1 / ((A+r)*(A+r+1)) - 1 / A^2 + (2*r+1)*(1 / A^3)) ≤
      (4*r^3+6*r^2+4*r+1) * (1 / A^5) := by
  have hid : (4*r^3+6*r^2+4*r+1) * (1 / A^5) -
      ((3*r^2+3*r+1) * (1 / A^4) -
        (1 / ((A+r)*(A+r+1)) - 1 / A^2 + (2*r+1)*(1 / A^3))) =
      ((5*r^4+10*r^3+10*r^2+5*r+1)*A + (4*r^3+6*r^2+4*r+1)*r*(r+1)) /
        (A^5 * (A+r) * (A+r+1)) := by
    have hAr : A+r ≠ 0 := by positivity
    have hAr1 : A+r+1 ≠ 0 := by positivity
    field_simp [ne_of_gt hA, hAr, hAr1]
    <;> ring
  have hnonneg : 0 ≤ (4*r^3+6*r^2+4*r+1) * (1 / A^5) -
      ((3*r^2+3*r+1) * (1 / A^4) -
        (1 / ((A+r)*(A+r+1)) - 1 / A^2 + (2*r+1)*(1 / A^3))) := by
    rw [hid]
    positivity
  linarith

private theorem progressionTaylorSecondTerm_summable (Q r : ℕ) (hQ : 0 < Q) :
    Summable (progressionTaylorSecondTerm Q r) := by
  exact ((scaled_pSeries_summable Q 4 (by omega)).mul_left
    (3*(r : ℝ)^2+3*r+1)).sub (progressionTaylorTerm_summable Q r hQ)

private theorem progressionTaylorSecondRemainder_eq_tsum (Q r : ℕ) (hQ : 0 < Q) :
    progressionTaylorSecondRemainder Q r = ∑' j, progressionTaylorSecondTerm Q r j := by
  unfold progressionTaylorSecondRemainder progressionTaylorSecondTerm
  rw [Summable.tsum_sub ((scaled_pSeries_summable Q 4 (by omega)).mul_left
    (3*(r : ℝ)^2+3*r+1)) (progressionTaylorTerm_summable Q r hQ)]
  rw [tsum_mul_left, scaled_pSeries_tsum, progressionTaylorRemainder_eq_tsum Q r hQ]

/-- The fourth-order correction has a strictly negative remaining error;
this theorem bounds its positive magnitude by the explicit fifth-order term. -/
theorem progressionTaylorSecondRemainder_bounds (Q r : ℕ) (hQ : 0 < Q) :
    0 < progressionTaylorSecondRemainder Q r ∧
      progressionTaylorSecondRemainder Q r ≤
        (4*(r : ℝ)^3+6*r^2+4*r+1) * (positivePSeries 5 / (Q : ℝ)^5) := by
  have hterm (j : ℕ) : 0 < progressionTaylorSecondTerm Q r j := by
    unfold progressionTaylorSecondTerm progressionTaylorTerm
    rw [progression_tail_atom]
    exact inverse_product_second_remainder_pos _ _ (by positivity) (by positivity)
  rw [progressionTaylorSecondRemainder_eq_tsum Q r hQ]
  constructor
  · have hle := (progressionTaylorSecondTerm_summable Q r hQ).sum_le_tsum
      ({0} : Finset ℕ) (fun j _ => le_of_lt (hterm j))
    have hle' : progressionTaylorSecondTerm Q r 0 ≤ ∑' j, progressionTaylorSecondTerm Q r j := by
      simpa using hle
    exact (hterm 0).trans_le hle'
  · rw [← scaled_pSeries_tsum Q 5, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (progressionTaylorSecondTerm_summable Q r hQ)
      ((scaled_pSeries_summable Q 5 (by omega)).mul_left
        (4*(r : ℝ)^3+6*r^2+4*r+1))
    intro j
    unfold progressionTaylorSecondTerm progressionTaylorTerm
    rw [progression_tail_atom]
    exact inverse_product_second_remainder_le _ _ (by positivity) (by positivity)

/-- Fully signed expansion through the inverse-fourth-power term. It holds
for every positive Q and every nonnegative integer r. Its error is O_r(Q^-5),
with the complete r-dependent constant displayed rather than suppressed. -/
theorem progressionWeight_signed_taylor_fourth (Q r : ℕ) (hQ : 0 < Q) :
    progressionWeight Q r = positiveWeight r + Real.pi^2 / (6*(Q : ℝ)^2) -
      (2*(r : ℝ)+1) * positivePSeries 3 / (Q : ℝ)^3 +
      (3*(r : ℝ)^2+3*r+1) * Real.pi^4 / (90*(Q : ℝ)^4) -
      progressionTaylorSecondRemainder Q r ∧
    0 < progressionTaylorSecondRemainder Q r ∧
    progressionTaylorSecondRemainder Q r ≤
      (4*(r : ℝ)^3+6*r^2+4*r+1) * positivePSeries 5 / (Q : ℝ)^5 := by
  refine ⟨?_, (progressionTaylorSecondRemainder_bounds Q r hQ).1, ?_⟩
  · unfold progressionTaylorSecondRemainder progressionTaylorRemainder
    rw [positivePSeries_two, positivePSeries_four]
    ring
  · have h := (progressionTaylorSecondRemainder_bounds Q r hQ).2
    convert h using 1 <;> ring

end
end RiemannResearch.RH.Pareto
