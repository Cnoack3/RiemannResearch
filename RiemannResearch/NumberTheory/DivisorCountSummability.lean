import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Divisor-count summability for real exponents

This extends the square-denominator provider by the same standard Dirichlet
convolution identity ζ(s)^2 = ∑ τ(n)/n^s for s > 1. The formal input is Mathlib's
`LSeriesSummable.convolution`, with no divisor-growth assumption.

RH consumer: raw Möbius residual pairings against tests whose primitive is bounded
by a fixed power n^α with α < 1. This remains strictly an unconditional analytic
provider; it does not assert that the actual RH residual has this property.

-/

open scoped BigOperators

namespace RiemannResearch.NumberTheory

/-- Absolute convergence of the divisor-count Dirichlet series for real s > 1. -/
theorem summable_divisor_count_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) / (n : ℝ) ^ s) := by
  have h : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) (s : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (by intro n hn; simp) (by simpa using hs)
  have hc := h.convolution h
  change Summable (LSeries.term
    (LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (fun _ : ℕ => (1 : ℂ)))
      (s : ℂ)) at hc
  have he (n : ℕ) :
      LSeries.convolution (fun _ : ℕ => (1 : ℂ))
        (fun _ : ℕ => (1 : ℂ)) n = (n.divisors.card : ℂ) := by
    rw [LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℂ) * 1)]
    simp
  apply hc.norm.congr
  intro n
  rw [LSeries.norm_term_eq, he]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

/-- Adding a fixed constant to the divisor count preserves convergence for s > 1. -/
theorem summable_const_add_divisor_count_div_rpow (c s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (c + (n.divisors.card : ℝ)) / (n : ℝ) ^ s) := by
  have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) :=
    Real.summable_one_div_nat_rpow.mpr hs
  simpa only [add_div, mul_one_div] using
    (hp.mul_left c).add (summable_divisor_count_div_rpow s hs)

/-- The raw residual's variation majorant remains summable after multiplication
by any fixed power of its index with exponent strictly smaller than one. -/
theorem summable_rpow_mul_divisor_count_successor_majorant
    (α : ℝ) (hα : α < 1) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ α *
      ((3 + ((k + 1).divisors.card : ℝ)) /
        (((k : ℝ) + 1) * ((k : ℝ) + 2)))) := by
  have hsum := summable_const_add_divisor_count_div_rpow 3 (2 - α) (by linarith)
  have hshift : Summable (fun k : ℕ =>
      (3 + ((k + 1).divisors.card : ℝ)) / ((k : ℝ) + 1) ^ (2 - α)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hsum
  apply hshift.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    have hx : 0 < (k : ℝ) + 1 := by positivity
    have hxp : 0 ≤ ((k : ℝ) + 1) ^ α := (Real.rpow_pos_of_pos hx α).le
    rw [← mul_div_assoc]
    calc
      ((k : ℝ) + 1) ^ α * (3 + ((k + 1).divisors.card : ℝ)) /
          (((k : ℝ) + 1) * ((k : ℝ) + 2))
          ≤ ((k : ℝ) + 1) ^ α * (3 + ((k + 1).divisors.card : ℝ)) /
            ((k : ℝ) + 1) ^ 2 := by
              apply div_le_div_of_nonneg_left (by positivity) (by positivity)
              nlinarith [show (0 : ℝ) ≤ k by positivity]
      _ = (3 + ((k + 1).divisors.card : ℝ)) /
          ((k : ℝ) + 1) ^ (2 - α) := by
            rw [Real.rpow_sub hx, Real.rpow_two, div_div_eq_mul_div]
            ring

/-- The square-denominator case. -/
theorem summable_divisor_count_div_sq :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) / (n : ℝ) ^ 2) := by
  simpa only [Real.rpow_two] using
    summable_divisor_count_div_rpow 2 (by norm_num)

/-- A shifted majorant for the first difference of the raw Möbius residual. -/
theorem summable_divisor_count_successor_majorant :
    Summable (fun k : ℕ => (3 + ((k + 1).divisors.card : ℝ)) /
      (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  simpa only [Real.rpow_zero, one_mul] using
    summable_rpow_mul_divisor_count_successor_majorant 0 (by norm_num)

end RiemannResearch.NumberTheory
