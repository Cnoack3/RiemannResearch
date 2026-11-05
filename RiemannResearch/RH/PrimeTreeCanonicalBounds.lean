/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.PrimeTreeCanonicalCarry
import RiemannResearch.RH.PrimeTreeUniformCarry
import RiemannResearch.RH.PrimeTreeSingleLiftBounds
import Mathlib.Tactic

/-! # Exact edge data and first moment of the consecutive-prime carry law

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
the table in §3 and the final §5.1 estimate. The tail denominator 955 is
obtained by retaining the three known noninitial contributions exactly.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CanonicalPrimeCarry
open CRTCarryArithmetic PrimeTreeSingleLiftBounds

theorem next_three_inverses :
    positiveInverse 1 = 5 ∧ positiveInverse 2 = 13 ∧ positiveInverse 3 = 191 := by
  have h1 := inverse_spec 1
  have h2 := inverse_spec 2
  have h3 := inverse_spec 3
  norm_num [primorialAt, radix, primeAt, Finset.prod_range_succ] at h1 h2 h3
  omega

def absPrimeCoefficient (k : ℕ) : ℝ := |firstChain.w (k+1) * (firstChain.b k : ℝ)|

theorem first_three_tail_coefficients : absPrimeCoefficient 1 = 4/5 ∧
    absPrimeCoefficient 2 = 3/65 ∧ absPrimeCoefficient 3 = 10/12415 ∧
    firstChain.w 4 = 1/12415 := by
  obtain ⟨h1, h2, h3⟩ := next_three_inverses
  norm_num [absPrimeCoefficient, firstChain, weight, carryPartner, primorialAt, radix, primeAt,
    Finset.prod_range_succ, inverse_zero, h1, h2, h3]

theorem canonical_firstMoment :
    Summable (fun k => absPrimeCoefficient (k+1)) ∧
      (∑' k, absPrimeCoefficient (k+1)) ≤ 809/955 := by
  obtain ⟨h1, h2, h3, hw4⟩ := first_three_tail_coefficients
  have ht := firstChain.primeWeight_tail (fun k => (weight_pos k).le) weight_antitone_step
    (fun k => by change (2 : ℤ) ≤ (positiveInverse (k+1) : ℤ); exact_mod_cast inverse_after_first k)
    radix_le_prefix 4 (by decide)
  have ht' : Summable (fun k => absPrimeCoefficient (k+4)) ∧
      (∑' k, absPrimeCoefficient (k+4)) ≤ 2 * firstChain.w 4 := ht
  have hs : Summable (fun k => absPrimeCoefficient (k+1)) :=
    (summable_nat_add_iff 3).mp ht'.1
  refine ⟨hs, ?_⟩
  have h := hs.sum_add_tsum_nat_add 3
  norm_num [Finset.sum_range_succ, h1, h2, h3, Nat.add_assoc] at h
  rw [hw4] at ht'
  linarith [ht'.2]

theorem edgeMass_mul_radix (k : ℕ) :
    firstChain.edgeMass k * (radix k : ℝ) = 2 * absPrimeCoefficient k := by
  have hm : 1 % firstChain.p k = 1 := Nat.mod_eq_of_lt (firstChain.radix_ge k)
  have hp : (firstChain.p k : ℝ) ≠ 0 := by
    exact_mod_cast (primeAt_prime (k+1)).ne_zero
  have h := firstChain.primeTerm_eq 1 k
  simp only [NormalizedCarryChain.primeTerm, ArithmeticCumulative.residueFraction,
    hm, Nat.cast_one, one_mul] at h
  have he : firstChain.edgeMass k * (firstChain.p k : ℝ) =
      -2 * (firstChain.w (k+1) * (firstChain.b k : ℝ)) := by
    unfold NormalizedCarryChain.edgeMass
    have hp' := (div_eq_iff hp).mp (show firstChain.w (k+1) * (firstChain.b k : ℝ) /
        (firstChain.p k : ℝ) = _ by simpa [div_eq_mul_inv] using h)
    simp only [div_eq_mul_inv] at *
    linear_combination 2 * hp'
  have hmpos := (firstChain_probability.2 k).le
  have hn : firstChain.w (k+1) * (firstChain.b k : ℝ) ≤ 0 := by
    linarith [mul_nonneg hmpos (Nat.cast_nonneg (firstChain.p k) : (0 : ℝ) ≤ firstChain.p k)]
  change firstChain.edgeMass k * (firstChain.p k : ℝ) = 2 * |firstChain.w (k+1) * (firstChain.b k : ℝ)|
  rw [he, abs_of_nonpos hn]
  ring

/-- The U=5 normalized factor uses only the explicitly constructed edge law.
The bound has no remaining first-moment hypothesis. -/
theorem canonical_fiveFactor_lower (s : ℂ) (h0 : 0 ≤ s.re) (hh : s.re ≤ 1/2) :
    (1/300 : ℝ) < ‖fiveFactor (fun k => (radix (k+1) : ℝ)/3)
      (fun k => firstChain.edgeMass (k+1)/5) s‖ := by
  have hq (k : ℕ) : 1 ≤ (radix (k+1) : ℝ)/3 := by
    have hm : StrictMono primeAt := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    have hh := hm.monotone (show 1 ≤ k+1+1 by omega)
    have hb : primeAt 1 = 3 := Nat.nth_prime_one_eq_three
    rw [hb] at hh
    have hh' : (3 : ℝ) ≤ (radix (k+1) : ℝ) := by exact_mod_cast hh
    linarith
  have hm (k : ℕ) : (firstChain.edgeMass (k+1)/5) * ((radix (k+1) : ℝ)/3) =
      (2/15 : ℝ) * absPrimeCoefficient (k+1) := by
    linear_combination (1/15 : ℝ) * edgeMass_mul_radix (k+1)
  apply fiveFactor_norm_lower _ _ hq (fun k => div_nonneg (firstChain_probability.2 (k+1)).le (by norm_num))
    ((2/15 : ℝ) * ∑' k, absPrimeCoefficient (k+1)) _ _ s h0 hh
  · simpa only [hm] using canonical_firstMoment.1.hasSum.mul_left (2/15 : ℝ)
  · linarith [canonical_firstMoment.2]

end RiemannResearch.RH.CanonicalPrimeCarry
