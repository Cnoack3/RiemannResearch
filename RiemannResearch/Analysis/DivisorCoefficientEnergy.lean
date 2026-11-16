/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Elementary logarithmic energy for divisor coefficients

The actual fourth-moment problem needs the coefficient energy
`sum_{n <= N} d(n)^2 / n = O(log(N)^4)`.
We prove the elementary majorization `d(n)^2 <= (d * d)(n)` and a
reciprocally weighted convolution inequality. No asymptotic divisor estimate
or zeta-moment premise is needed.

Source for the analytic application: Chourasiya--Simonic,
https://arxiv.org/html/2507.15184v2, Sections 5.1--5.2.
The proof below uses finite convolution and harmonic sums; it does not
formalize the analytic representation from that source.
-/
noncomputable section
open scoped BigOperators

namespace ArithmeticFunction

/-- Dividing the coefficient at `n` by `n`, with the value at zero retained. -/
def reciprocalWeight (f : ArithmeticFunction ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => (f n : ℝ) / n, by simp⟩

@[simp] theorem reciprocalWeight_apply (f : ArithmeticFunction ℕ) (n : ℕ) :
    reciprocalWeight f n = (f n : ℝ) / n := rfl

/-- Exact compatibility of reciprocal weights with Dirichlet convolution. -/
theorem reciprocalWeight_mul (f g : ArithmeticFunction ℕ) :
    reciprocalWeight (f * g) = reciprocalWeight f * reciprocalWeight g := by
  ext n
  simp only [reciprocalWeight_apply, mul_apply, Nat.cast_sum, Nat.cast_mul,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have he : (p.1 : ℝ) * p.2 = n := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [div_mul_div_comm, he]

/-- Exact finite convolution formula, before dropping the hyperbolic cutoff. -/
theorem sum_reciprocal_mul_eq (f g : ArithmeticFunction ℕ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℝ) / n) =
      ∑ p ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun p => p.1 * p.2 ≤ N),
        ((f p.1 : ℝ) / p.1) * ((g p.2 : ℝ) / p.2) := by
  simpa only [reciprocalWeight_apply, ← reciprocalWeight_mul] using
    sum_Ioc_mul_eq_sum_prod_filter (reciprocalWeight f) (reciprocalWeight g) N

/-- A uniform finite weighted convolution bound, with constant one. -/
theorem sum_reciprocal_mul_le (f g : ArithmeticFunction ℕ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℝ) / n) ≤
      (∑ n ∈ Finset.Ioc 0 N, (f n : ℝ) / n) *
        (∑ n ∈ Finset.Ioc 0 N, (g n : ℝ) / n) := by
  rw [sum_reciprocal_mul_eq]
  calc
    _ ≤ ∑ p ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N,
        ((f p.1 : ℝ) / p.1) * ((g p.2 : ℝ) / p.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by rw [Finset.sum_product, Finset.sum_mul_sum]

/-- At prime powers each summand in the convolution dominates `k+1`. -/
theorem sigma_zero_sq_le_convolution_prime_pow {p k : ℕ} (hp : p.Prime) :
    sigma 0 (p ^ k) ^ 2 ≤ (sigma 0 * sigma 0) (p ^ k) := by
  rw [sigma_zero_apply_prime_pow hp, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => sigma 0 a * sigma 0 b),
    Nat.sum_divisors_prime_pow hp]
  calc
    (k + 1) ^ 2 = ∑ j ∈ Finset.range (k + 1), (k + 1) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
      have hdiv : p ^ k / p ^ j = p ^ (k - j) := by
        conv_lhs => rw [show p ^ k = p ^ (k - j) * p ^ j by
          rw [← pow_add, Nat.sub_add_cancel hjk]]
        exact Nat.mul_div_cancel _ (pow_pos hp.pos j)
      rw [hdiv, sigma_zero_apply_prime_pow hp,
        sigma_zero_apply_prime_pow hp]
      have he := Nat.sub_add_cancel hjk
      nlinarith [Nat.zero_le (j * (k - j))]

/-- The elementary bound `d(n)^2 <= d_4(n)` at every natural number. -/
theorem sigma_zero_sq_le_convolution (n : ℕ) :
    sigma 0 n ^ 2 ≤ (sigma 0 * sigma 0) n := by
  by_cases hn : n = 0
  · subst n; simp
  have hf := (isMultiplicative_sigma (k := 0)).ppow (k := 2)
  have hg := (isMultiplicative_sigma (k := 0)).mul (isMultiplicative_sigma (k := 0))
  rw [← ppow_apply (by norm_num : 0 < (2 : ℕ)),
    hf.multiplicative_factorization _ hn, hg.multiplicative_factorization _ hn]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p hp
  dsimp only
  rw [ppow_apply (by norm_num : 0 < (2 : ℕ))]
  exact sigma_zero_sq_le_convolution_prime_pow (Nat.prime_of_mem_primeFactors hp)

theorem sum_reciprocal_zeta_eq_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (zeta n : ℝ) / n) = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by ext n; simp; omega
  rw [hset]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [zeta_apply_ne (by have := (Finset.mem_Icc.mp hn).1; omega)]
  simp [one_div]

theorem sum_reciprocal_sigma_zero_le (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (sigma 0 n : ℝ) / n) ≤ (harmonic N : ℝ) ^ 2 := by
  have he : zeta * zeta = sigma 0 := by
    simpa only [pow_zero_eq_zeta] using (zeta_mul_pow_eq_sigma (k := 0))
  simpa only [he, sum_reciprocal_zeta_eq_harmonic, pow_two] using
    sum_reciprocal_mul_le zeta zeta N

/-- Sharp logarithmic degree, without a divisor-sum asymptotic. -/
theorem sum_sigma_zero_sq_div_le_harmonic_four (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (sigma 0 n : ℝ) ^ 2 / n) ≤ (harmonic N : ℝ) ^ 4 := by
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by ext n; simp; omega
  rw [hset]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, ((sigma 0 * sigma 0) n : ℝ) / n := by
      apply Finset.sum_le_sum
      intro n hn
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast sigma_zero_sq_le_convolution n
    _ ≤ (∑ n ∈ Finset.Ioc 0 N, (sigma 0 n : ℝ) / n) ^ 2 := by
      simpa only [pow_two] using sum_reciprocal_mul_le (sigma 0) (sigma 0) N
    _ ≤ ((harmonic N : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity))
        (sum_reciprocal_sigma_zero_le N) 2
    _ = _ := by ring

theorem sum_sigma_zero_sq_div_le_log_four (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (sigma 0 n : ℝ) ^ 2 / n) ≤ (1 + Real.log N) ^ 4 := by
  have hh : 0 ≤ (harmonic N : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  exact (sum_sigma_zero_sq_div_le_harmonic_four N).trans
    (pow_le_pow_left₀ hh (harmonic_le_one_add_log N) 4)

end ArithmeticFunction
