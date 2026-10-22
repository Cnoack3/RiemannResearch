/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.Ring

/-!
# Multiplicative coefficients from independently assigned prime ordinates

For each prime p, select a real ordinate gamma(p), set its phase to
exp(-i gamma(p) log p), and extend by unique factorization. The results hold
for arbitrary real assignments, hence also for assignments of actual zeta-zero
ordinates. No zero-distribution assertion or RH hypothesis is needed here.

The dummy value at natural zero is one; all multiplicativity statements are
on positive integers and Mathlib's L-series ignores the zero index.
`LSeriesSummable_coefficient_iff` concerns absolute (unordered) convergence,
not convergence of conditionally convergent partial sums.

Source: user-provided primewise-ordinate construction and corrected
Prime-Lattice Phase Cancellation handoff (October 13, 2026).
The terminology Helson zeta function for the associated unimodular Euler
product is standard; see K. Seip, https://arxiv.org/abs/1812.11729.
The full Euler product and analytic continuation are discussed separately in
`RH/PrimeOrdinateTwistResearch20261013.md`; they are not asserted here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.PrimeOrdinateTwist

/-- Completely multiplicative extension on positive integers. The dummy value
at zero is one and is ignored by `LSeries.term`. -/
def primeExtension (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  n.factorization.prod (fun p k => a p ^ k)

@[simp] theorem primeExtension_one (a : ℕ → ℂ) : primeExtension a 1 = 1 := by
  simp [primeExtension]

theorem primeExtension_mul (a : ℕ → ℂ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primeExtension a (m * n) = primeExtension a m * primeExtension a n := by
  simp only [primeExtension, Nat.factorization_mul hm hn]
  apply Finsupp.prod_add_index
  · intros; simp
  · intros; simp [pow_add]

@[simp] theorem primeExtension_prime (a : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    primeExtension a p = a p := by
  simp [primeExtension, hp.factorization]

theorem primeExtension_pow (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    primeExtension a (n ^ k) = primeExtension a n ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, primeExtension_mul a (pow_ne_zero _ hn) hn, ih, pow_succ]

theorem primeExtension_prime_pow (a : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeExtension a (p ^ k) = a p ^ k := by
  rw [primeExtension_pow a hp.ne_zero, primeExtension_prime a hp]

/-- Values at nonprimes have no effect on the extension. -/
theorem primeExtension_congr {a b : ℕ → ℂ}
    (hab : ∀ p, p.Prime → a p = b p) (n : ℕ) :
    primeExtension a n = primeExtension b n := by
  simp only [primeExtension, Finsupp.prod]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : p.Prime
  · rw [hab p hp]
  · simp [Nat.factorization_eq_zero_of_not_prime n hp]

/-- Equality of the extensions is exactly equality of the prime phases. -/
theorem primeExtension_eq_iff (a b : ℕ → ℂ) :
    (∀ n, n ≠ 0 → primeExtension a n = primeExtension b n) ↔
      ∀ p, p.Prime → a p = b p := by
  constructor
  · intro h p hp
    simpa only [primeExtension_prime a hp, primeExtension_prime b hp] using h p hp.ne_zero
  · intro h n _
    exact primeExtension_congr h n

theorem norm_primeExtension (a : ℕ → ℂ) (ha : ∀ p, ‖a p‖ = 1) (n : ℕ) :
    ‖primeExtension a n‖ = 1 := by
  simp [primeExtension, Finsupp.prod, norm_prod, ha]

/-- The negative phase convention agrees with the vertical shift s + iγ. -/
def primePhase (γ : ℕ → ℝ) (p : ℕ) : ℂ :=
  Complex.exp (-Complex.I * ((γ p * Real.log p : ℝ) : ℂ))

@[simp] theorem norm_primePhase (γ : ℕ → ℝ) (p : ℕ) : ‖primePhase γ p‖ = 1 := by
  rw [primePhase, Complex.norm_exp]
  have h : (-Complex.I * ((γ p * Real.log p : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h, Real.exp_zero]

def coefficient (γ : ℕ → ℝ) : ℕ → ℂ := primeExtension (primePhase γ)

theorem coefficient_mul (γ : ℕ → ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    coefficient γ (m * n) = coefficient γ m * coefficient γ n :=
  primeExtension_mul _ hm hn

theorem coefficient_prime_pow (γ : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    coefficient γ (p ^ k) = primePhase γ p ^ k :=
  primeExtension_prime_pow _ hp k

@[simp] theorem norm_coefficient (γ : ℕ → ℝ) (n : ℕ) : ‖coefficient γ n‖ = 1 :=
  norm_primeExtension _ (norm_primePhase γ) n

/-- Independent ordinates preserve exactly the absolute-convergence boundary. -/
theorem LSeriesSummable_coefficient_iff (γ : ℕ → ℝ) (s : ℂ) :
    LSeriesSummable (coefficient γ) s ↔ 1 < s.re := by
  have hnorm : (fun n => ‖LSeries.term (coefficient γ) s n‖) =
      (fun n => ‖LSeries.term 1 s n‖) := by
    funext n
    simp [LSeries.norm_term_eq]
  change Summable (LSeries.term (coefficient γ) s) ↔ _
  rw [← summable_norm_iff, hnorm, summable_norm_iff]
  exact LSeriesSummable_one_iff

end RiemannResearch.Analysis.PrimeOrdinateTwist

end
