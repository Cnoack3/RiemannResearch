/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteIncidenceTailCharge
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite signed mass budgets from centered squares

Source: standard finite Cauchy-Schwarz and the Jordan decomposition.
The RH consumer is the signed tail on a complete gcd class. All variances
are unweighted sums of squares; bounding them asymptotically is separate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteIncidenceTailCharge

theorem sum_abs_eq_positive_add_negative {α : Type*}
    (s : Finset α) (x : α → ℝ) :
    (∑ a ∈ s, |x a|) = positiveCharge s x + negativeCharge s x := by
  unfold positiveCharge negativeCharge
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rcases le_total 0 (x a) with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add]

/-- A quadratic budget for the negative mass, retaining the entire centered
square sum. No assertion of nonnegative individual charges is used. -/
theorem negative_charge_quadratic_budget {α : Type*}
    (s : Finset α) (x : α → ℝ) (c : ℝ)
    (hmean : (∑ a ∈ s, x a) = (s.card : ℝ) * c) :
    4 * negativeCharge s x *
        (negativeCharge s x + (s.card : ℝ) * c) ≤
      (s.card : ℝ) * ∑ a ∈ s, (x a - c)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun a => |x a|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
    mul_one, sq_abs] at hcs
  rw [sum_abs_eq_positive_add_negative,
    sum_sq_eq_mean_sq_add_centered_sq s x c hmean] at hcs
  have hj := positive_sub_negative s x
  rw [hmean] at hj
  have hp : positiveCharge s x = negativeCharge s x + (s.card : ℝ) * c := by
    linarith
  rw [hp] at hcs
  nlinarith

/-- Direct linear variance budget, also valid without a class mean. -/
theorem negative_charge_linear_budget {α : Type*}
    (s : Finset α) (x : α → ℝ) (c : ℝ) :
    4 * c * negativeCharge s x ≤ ∑ a ∈ s, (x a - c)^2 := by
  unfold negativeCharge
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  by_cases h : 0 ≤ x a
  · rw [max_eq_right (neg_nonpos.mpr h), mul_zero]
    exact sq_nonneg _
  · rw [max_eq_left (by linarith : 0 ≤ -x a)]
    nlinarith [sq_nonneg (x a + c)]

theorem negative_charge_eq_erase_of_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ) (a : α) (ha : a ∈ s) (hx : 0 ≤ x a) :
    negativeCharge s x = negativeCharge (s.erase a) x := by
  have h := Finset.sum_erase_add (s := s) (f := fun k => max (-x k) 0) ha
  rw [max_eq_right (neg_nonpos.mpr hx), add_zero] at h
  exact h.symm

end RiemannResearch.Analysis.FiniteIncidenceTailCharge
