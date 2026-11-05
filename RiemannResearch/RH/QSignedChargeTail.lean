/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSignedTailRigidity
import RiemannResearch.RH.QPhysicalTailEnergy

/-! # Absolute tails of the charge of a complete-Q vector

A scalar Young inequality and the telescoping Pareto tail give a uniform
cutoff bound on total variation. No orthogonality hypothesis enters here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSignedTailRigidity
open ZetaTwoHilbert ZetaTwoProbability

/-- The mass of the complete charge outside the physical coordinates `0,…,X`.
The input scale is real, allowing the estimate to be used directly on prime
scales with a factor comparable to the square root of the cutoff. -/
theorem scaled_absoluteCoefficient_tail_le (u : QHilbert) (X : ℕ) (R : ℝ)
    (hR : R ^ 2 ≤ (X : ℝ) + 1) :
    R * (∑' n : ℕ, if n ∈ Finset.range (X + 1) then 0 else |signedCoefficient u n|) ≤
      ‖u‖ ^ 2 + 2 / zetaTwo := by
  let L := X + 1
  let a := fun n : ℕ => if n ∈ Finset.range L then (0 : ℝ) else |signedCoefficient u n|
  have ht (j : ℕ) : a (j + L) = |signedCoefficient u (j + L)| := by
    simp only [a, Finset.mem_range, if_neg (by omega : ¬ j + L < L)]
  have hb : Summable (fun j : ℕ => |signedCoefficient u (j + L)|) :=
    (summable_nat_add_iff L).mpr (signedCoefficient_summable u).abs
  have ha : Summable (fun j : ℕ => a (j + L)) := by simpa only [ht] using hb
  have htail : (∑' n, a n) = ∑' j : ℕ, |signedCoefficient u (j + L)| := by
    have he := Summable.sum_add_tsum_nat_add' (f := a) (k := L) ha
    have hz : (∑ n ∈ Finset.range L, a n) = 0 := by
      exact Finset.sum_eq_zero (fun n hn => by simp only [a, if_pos hn])
    rw [hz, zero_add] at he
    simpa only [ht] using he.symm
  have hE := (summable_nat_add_iff (f := fun n => positiveQWeight n * qSequence u n ^ 2) L).mpr
    (qSequence_square_summable u)
  have hEbound : (∑' j : ℕ, positiveQWeight (j + L) * qSequence u (j + L) ^ 2) ≤ ‖u‖ ^ 2 := by
    have he := (qSequence_square_summable u).sum_add_tsum_nat_add L
    have hz : 0 ≤ ∑ n ∈ Finset.range L, positiveQWeight n * qSequence u n ^ 2 :=
      Finset.sum_nonneg (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
    rw [qNorm_weighted_sq]
    linarith
  have hP := (summable_nat_add_iff (f := Pareto.positiveWeight) L).mpr Pareto.positiveWeight_summable
  have hpow : 0 ≤ R ^ 2 := sq_nonneg _
  have hZ := zetaTwo_pos
  let c := (2 / zetaTwo) * R ^ 2
  have hpt (j : ℕ) : R * |signedCoefficient u (j + L)| ≤
      positiveQWeight (j + L) * qSequence u (j + L) ^ 2 + c * Pareto.positiveWeight (j + L) := by
    let n := j + L
    have hY : R * |qSequence u n| ≤ qSequence u n ^ 2 + R ^ 2 := by
      nlinarith only [sq_nonneg (|qSequence u n| - R), sq_nonneg (qSequence u n),
        sq_nonneg R, sq_abs (qSequence u n)]
    have hW : positiveQWeight n ≤ (2 / zetaTwo) * Pareto.positiveWeight n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hZ]
      simpa only [mul_comm] using
        ZetaTwoParetoTransfer.zetaTwo_mul_QWeight_le_two_mul_paretoWeight n
    change R * |positiveQWeight n * qSequence u n| ≤ _
    rw [abs_mul, abs_of_nonneg (positiveQWeight_nonneg _)]
    calc
      _ = positiveQWeight n * (R * |qSequence u n|) := by ring
      _ ≤ positiveQWeight n * (qSequence u n ^ 2 + R ^ 2) :=
        mul_le_mul_of_nonneg_left hY (positiveQWeight_nonneg n)
      _ ≤ _ := by
        rw [mul_add]
        change _ ≤ positiveQWeight n * qSequence u n ^ 2 + c * Pareto.positiveWeight n
        apply add_le_add_right
        calc
          _ ≤ ((2 / zetaTwo) * Pareto.positiveWeight n) * R ^ 2 :=
            mul_le_mul_of_nonneg_right hW hpow
          _ = _ := by dsimp [c]; ring
  have hmain := (hb.mul_left R).tsum_le_tsum hpt (hE.add (hP.mul_left c))
  change R * (∑' n, a n) ≤ _
  rw [htail, ← tsum_mul_left]
  refine hmain.trans ?_
  rw [hE.tsum_add (hP.mul_left c), tsum_mul_left, Pareto.positiveWeight_tail_tsum L (by dsimp [L]; omega)]
  apply add_le_add hEbound
  have hL : (0 : ℝ) < L := by dsimp [L]; positivity
  have hRL : R ^ 2 ≤ (L : ℝ) := by simpa [L] using hR
  change (2 / zetaTwo * R ^ 2) * (1 / (L : ℝ)) ≤ 2 / zetaTwo
  rw [mul_one_div, div_le_iff₀ hL]
  exact mul_le_mul_of_nonneg_left hRL (div_nonneg (by norm_num) hZ.le)

/-- Uniform inverse-square-root tail bound used for cofinal cutoffs. -/
theorem absoluteCoefficient_tail_le_div_sqrt (u : QHilbert) (X : ℕ) :
    (∑' n : ℕ, if n ∈ Finset.range (X + 1) then 0 else |signedCoefficient u n|) ≤ (‖u‖ ^ 2 + 2 / zetaTwo) / Real.sqrt ((X : ℝ) + 1) := by
  apply (le_div_iff₀ (Real.sqrt_pos.2 (by positivity))).2
  rw [mul_comm]
  exact scaled_absoluteCoefficient_tail_le u X _ (Real.sq_sqrt (by positivity)).le

end RiemannResearch.RH.QSignedTailRigidity
