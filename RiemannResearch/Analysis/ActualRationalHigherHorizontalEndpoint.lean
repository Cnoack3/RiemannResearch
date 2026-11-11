/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalHorizontalEndpoint
import RiemannResearch.Analysis.ActualRationalLandauLogPowers

/-!
# Higher retained horizontal corrections at rational frequencies

Source: Section 6 of `FRZ_Strengthening_2026-11-10.pdf`. All retained even
horizontal moments keep their exact signed coefficients. The zero mode is
centered before any norm estimate. The order is fixed throughout the
asymptotic conclusions; there is no assertion for an order growing with T.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The (j+1)-st nonconstant even horizontal Taylor term. -/
def rationalHorizontalTaylorTerm (T : ℝ) (n m j : ℕ) : ℂ :=
  ((Real.log ((n : ℝ) / (m : ℝ)) : ℂ) ^ (2 * (j + 1)) /
    (Nat.factorial (2 * (j + 1)) : ℂ)) *
      (evenHorizontalMoment T (Real.log ((n : ℝ) / (m : ℝ))) (j + 1) / (T : ℂ))

/-- Retain the first J nonconstant even horizontal moments. -/
def higherCorrectedRationalRemainder (T : ℝ) (n m J : ℕ) : ℂ :=
  centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m +
    ∑ j ∈ Finset.range J, rationalHorizontalTaylorTerm T n m j

theorem higherCorrectedRationalRemainder_one (T : ℝ) (n m : ℕ) :
    higherCorrectedRationalRemainder T n m 1 = correctedRationalRemainder T n m := by
  norm_num [higherCorrectedRationalRemainder, correctedRationalRemainder,
    rationalHorizontalTaylorTerm, rationalHorizontalCorrection, Finset.sum_range_succ]

theorem higherCorrectedRationalRemainder_succ (T : ℝ) (n m J : ℕ) :
    higherCorrectedRationalRemainder T n m (J + 1) =
      higherCorrectedRationalRemainder T n m J + rationalHorizontalTaylorTerm T n m J := by
  simp only [higherCorrectedRationalRemainder, Finset.sum_range_succ]
  ring

theorem horizontalTaylorPolynomial_eq_ordinate_add (T u : ℝ) (J : ℕ) :
    horizontalTaylorPolynomial T u J = ordinateSum T u +
      ∑ j ∈ Finset.range J,
        ((u : ℂ) ^ (2 * (j + 1)) / (Nat.factorial (2 * (j + 1)) : ℂ)) *
          evenHorizontalMoment T u (j + 1) := by
  rw [horizontalTaylorPolynomial_eq_moments, Finset.sum_range_succ']
  simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, one_mul, evenHorizontalMoment_zero]
  ring

theorem higherCorrectedRationalRemainder_eq_taylor_landau
    (T : ℝ) (hT : T ≠ 0) {n m : ℕ} (hmn : m < n) (J : ℕ) :
    higherCorrectedRationalRemainder T n m J =
      horizontalTaylorError T (Real.log ((n : ℝ) / (m : ℝ))) J / (T : ℂ) +
      (landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ) := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  have hne : n ≠ m := by omega
  simp only [higherCorrectedRationalRemainder, centeredRationalOrdinate,
    rationalFMZMain, if_neg hne, if_pos hmn, sub_zero, sub_neg_eq_add,
    horizontalTaylorError, horizontalTaylorPolynomial_eq_ordinate_add,
    rationalHorizontalTaylorTerm]
  have hsum (f g : ℕ → ℂ) : (∑ j ∈ Finset.range J, f j * (g j / (T : ℂ))) =
      (∑ j ∈ Finset.range J, f j * g j) / (T : ℂ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  push_cast
  field_simp
  <;> ring

theorem higherCorrectedRationalRemainder_self
    (T : ℝ) (n J : ℕ) (hn : 1 ≤ n) :
    higherCorrectedRationalRemainder T n n J = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp [higherCorrectedRationalRemainder, centeredRationalOrdinate, rationalFMZMain,
    rationalHorizontalTaylorTerm, hn0]

theorem rationalHorizontalTaylorTerm_swap (T : ℝ) (n m j : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    rationalHorizontalTaylorTerm T n m j = star (rationalHorizontalTaylorTerm T m n j) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hl : Real.log ((n : ℝ) / (m : ℝ)) =
      -Real.log ((m : ℝ) / (n : ℝ)) := by
    rw [Real.log_div hn0 hm0, Real.log_div hm0 hn0]
    ring
  simp [rationalHorizontalTaylorTerm, hl, pow_mul, evenHorizontalMoment_neg]

theorem higherCorrectedRationalRemainder_swap (T : ℝ) (n m J : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    higherCorrectedRationalRemainder T n m J =
      star (higherCorrectedRationalRemainder T m n J) := by
  have hterm := rationalHorizontalTaylorTerm_swap T n m
  have hbase := correctedRationalRemainder_swap T n m hn hm
  have hc : rationalHorizontalCorrection T n m = star (rationalHorizontalCorrection T m n) := by
    simpa [rationalHorizontalTaylorTerm, rationalHorizontalCorrection] using hterm 0 hn hm
  simp only [correctedRationalRemainder, star_add] at hbase
  have hh : centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m =
      star (centeredRationalOrdinate T m n / (T : ℂ) - rationalFMZMain m n) := by
    rw [hc] at hbase
    exact add_right_cancel hbase
  rw [higherCorrectedRationalRemainder, higherCorrectedRationalRemainder, star_add, hh]
  congr 1
  simp only [star_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact hterm j hn hm

end RiemannResearch.Analysis.ActualZeroOrdinate
