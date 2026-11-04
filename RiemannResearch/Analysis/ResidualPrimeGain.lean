/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ResidualGainProduct
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal-prime lower bounds for exact residual gains

Source: Euler's divergence theorem, as formalized in Mathlib's
NumberTheory.SumPrimeReciprocals following the Erdos proof in
Aigner and Ziegler, Proofs from THE BOOK, and the elementary product estimate
already proved in ResidualGainProduct.

Concrete RH consumer: orthogonal projection onto squarefree primorial
residue spaces. Their new orthonormal prime blocks have exact squared-energy
gains. If the relative gain at each prime p is at least c / p for one c > 0,
the residual tends to zero. This module proves the scalar conditional
implication and its finite exponential bound. It does not prove the
arithmetic lower bound, identify a numerical pattern with a theorem, or
formalize the application here; QPrimorialRelativeGain supplies that application.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ResidualGain

def primeReciprocal (n : ℕ) : ℝ :=
  if n.Prime then 1 / (n : ℝ) else 0

theorem primeReciprocal_nonneg (n : ℕ) : 0 ≤ primeReciprocal n := by
  unfold primeReciprocal
  split_ifs <;> positivity

theorem primeReciprocal_not_summable : ¬ Summable primeReciprocal := by
  have he : primeReciprocal =
      Set.indicator {n : ℕ | n.Prime} (fun n : ℕ => (1 : ℝ) / n) := by
    funext n
    simp [primeReciprocal, Set.indicator_apply]
  rw [he]
  exact not_summable_one_div_on_primes

theorem not_summable_of_prime_lower {r : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hr : ∀ n, 0 ≤ r n)
    (hlower : ∀ p : ℕ, p.Prime → c / (p : ℝ) ≤ r p) :
    ¬ Summable r := by
  intro hs
  have hsmall : Summable (fun n => c * primeReciprocal n) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg hc.le (primeReciprocal_nonneg n)) _ hs
    intro n
    by_cases hn : n.Prime
    · simpa [primeReciprocal, hn, div_eq_mul_inv] using hlower n hn
    · simpa [primeReciprocal, hn] using hr n
  apply primeReciprocal_not_summable
  simpa [← mul_assoc, ne_of_gt hc] using hsmall.mul_left c⁻¹

theorem residual_le_exp_neg_prime_sum {d r : ℕ → ℝ} {c : ℝ}
    (hd : 0 ≤ d 0) (h0 : ∀ n, 0 ≤ r n) (h1 : ∀ n, r n ≤ 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n))
    (hlower : ∀ p : ℕ, p.Prime → c / (p : ℝ) ≤ r p) (N : ℕ) :
    d N ≤ d 0 * Real.exp (-c * ∑ n ∈ Finset.range N, primeReciprocal n) := by
  have hsum : c * ∑ n ∈ Finset.range N, primeReciprocal n ≤
      ∑ n ∈ Finset.range N, r n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hnmem
    by_cases hn : n.Prime
    · simpa [primeReciprocal, hn, div_eq_mul_inv] using hlower n hn
    · simpa [primeReciprocal, hn] using h0 n
  rw [recurrence_eq_mul_product hrec]
  apply mul_le_mul_of_nonneg_left _ hd
  refine (survivalProduct_le_exp_neg_sum h1 N).trans ?_
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The prime lower bound is an assumption, not an arithmetic estimate. -/
theorem residual_tendsto_zero_of_prime_gain {d r : ℕ → ℝ} {c : ℝ}
    (hd : 0 < d 0) (h0 : ∀ n, 0 ≤ r n) (h1 : ∀ n, r n < 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n))
    (hc : 0 < c)
    (hlower : ∀ p : ℕ, p.Prime → c / (p : ℝ) ≤ r p) :
    Tendsto d atTop (𝓝 0) :=
  (residual_tendsto_zero_iff_not_summable hd h0 h1 hrec).mpr
    (not_summable_of_prime_lower hc h0 hlower)


/-- Removing a finite prime prefix does not remove reciprocal-prime divergence. -/
theorem not_summable_of_shifted_prime_lower {r : ℕ → ℝ} {c : ℝ}
    (offset : ℕ) (hc : 0 < c) (hr : ∀ n, 0 ≤ r n)
    (hlower : ∀ n, (n + offset).Prime → c / ((n + offset : ℕ) : ℝ) ≤ r n) :
    ¬ Summable r := by
  intro hs
  have hsmall : Summable (fun n => c * primeReciprocal (n + offset)) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg hc.le (primeReciprocal_nonneg _)) _ hs
    intro n
    by_cases hn : (n + offset).Prime
    · simpa [primeReciprocal, hn, div_eq_mul_inv] using hlower n hn
    · simpa [primeReciprocal, hn] using hr n
  have hall : Summable (fun n => c * primeReciprocal n) :=
    (summable_nat_add_iff offset).mp hsmall
  apply primeReciprocal_not_summable
  simpa [← mul_assoc, ne_of_gt hc] using hall.mul_left c⁻¹

end RiemannResearch.Analysis.ResidualGain
