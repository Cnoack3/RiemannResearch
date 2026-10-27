/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Nat.Factorization.Basic
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic fibers for actual prime-valuation resampling

The fiber through n fixes its p-free part and varies exactly the exponent
of the prime p. These are identities of natural numbers; no probability
space or independence assumption is used.
-/

namespace RiemannResearch.RH.PrimeResampling

/-- The p-free part of the positive integer n. -/
def primeCore (p n : ℕ) : ℕ := n / p ^ n.factorization p

/-- Replace the p-adic exponent of n by k, keeping its p-free part. -/
def replaceValuation (p n k : ℕ) : ℕ := primeCore p n * p ^ k

theorem primePower_mul_primeCore (p n : ℕ) :
    p ^ n.factorization p * primeCore p n = n :=
  Nat.ordProj_mul_ordCompl_eq_self n p

theorem primeCore_mul_primePower (p n : ℕ) :
    primeCore p n * p ^ n.factorization p = n := by
  rw [Nat.mul_comm]
  exact primePower_mul_primeCore p n

theorem primeCore_ne_zero (p n : ℕ) (hn : n ≠ 0) :
    primeCore p n ≠ 0 := by
  intro hz
  apply hn
  rw [← primePower_mul_primeCore p n, hz, Nat.mul_zero]

@[simp] theorem primeCore_eq_zero_iff (p n : ℕ) :
    primeCore p n = 0 ↔ n = 0 := by
  constructor
  · intro hz
    rw [← primePower_mul_primeCore p n, hz, Nat.mul_zero]
  · rintro rfl
    simp [primeCore]

theorem ne_zero_of_primeCore_eq (p n m : ℕ) (hn : n ≠ 0)
    (h : primeCore p m = primeCore p n) : m ≠ 0 := by
  intro hm
  have hzero : primeCore p n = 0 := by simpa [hm, primeCore] using h.symm
  exact primeCore_ne_zero p n hn hzero

theorem primeCore_pos (p n : ℕ) (hn : 0 < n) :
    0 < primeCore p n :=
  Nat.pos_of_ne_zero (primeCore_ne_zero p n (ne_of_gt hn))

theorem prime_not_dvd_primeCore (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ primeCore p n :=
  Nat.not_dvd_ordCompl hp hn

@[simp] theorem primeCore_factorization (p n : ℕ) :
    (primeCore p n).factorization p = 0 := by
  unfold primeCore
  rw [Nat.factorization_ordCompl]
  simp

theorem primeCore_eq_self_of_not_dvd (p n : ℕ) (hn : ¬p ∣ n) :
    primeCore p n = n := by
  unfold primeCore
  rw [Nat.factorization_eq_zero_of_not_dvd hn]
  simp

@[simp] theorem replaceValuation_self (p n : ℕ) :
    replaceValuation p n (n.factorization p) = n :=
  primeCore_mul_primePower p n

theorem replaceValuation_ne_zero (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    replaceValuation p n k ≠ 0 :=
  mul_ne_zero (primeCore_ne_zero p n hn) (pow_ne_zero k hp.ne_zero)

theorem replaceValuation_pos (p n k : ℕ) (hp : p.Prime) (hn : 0 < n) :
    0 < replaceValuation p n k :=
  Nat.pos_of_ne_zero (replaceValuation_ne_zero p n k hp (ne_of_gt hn))

@[simp] theorem factorization_replaceValuation
    (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    (replaceValuation p n k).factorization p = k := by
  unfold replaceValuation
  rw [Nat.factorization_mul (primeCore_ne_zero p n hn) (pow_ne_zero k hp.ne_zero)]
  simp only [Finsupp.add_apply, primeCore_factorization,
    Nat.factorization_pow_self hp, Nat.zero_add]

@[simp] theorem primeCore_replaceValuation
    (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    primeCore p (replaceValuation p n k) = primeCore p n := by
  change replaceValuation p n k / p ^ (replaceValuation p n k).factorization p = _
  rw [factorization_replaceValuation p n k hp hn]
  simpa only [replaceValuation, Nat.mul_comm] using
    (Nat.mul_div_cancel_left (primeCore p n) (pow_pos hp.pos k))

/-- Every exponent produces a different integer in the same arithmetic fiber. -/
theorem replaceValuation_injective (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    Function.Injective (replaceValuation p n) := by
  intro k l h
  have he := congrArg (fun m : ℕ => m.factorization p) h
  simpa only [factorization_replaceValuation p n k hp hn,
    factorization_replaceValuation p n l hp hn] using he

@[simp] theorem replaceValuation_eq_self_iff
    (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    replaceValuation p n k = n ↔ k = n.factorization p := by
  constructor
  · intro he
    apply replaceValuation_injective p n hp hn
    exact he.trans (replaceValuation_self p n).symm
  · rintro rfl
    exact replaceValuation_self p n

/-- Equality of p-free parts is exactly reachability by p-valuation resampling. -/
theorem primeCore_eq_iff_exists_replaceValuation
    (p n m : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    primeCore p n = primeCore p m ↔ ∃ k : ℕ, m = replaceValuation p n k := by
  constructor
  · intro h
    refine ⟨m.factorization p, ?_⟩
    unfold replaceValuation
    rw [h]
    exact (primeCore_mul_primePower p m).symm
  · rintro ⟨k, rfl⟩
    exact (primeCore_replaceValuation p n k hp hn).symm

/-- The exponent identifying a target in the same fiber is its actual valuation. -/
theorem replaceValuation_of_primeCore_eq
    (p n m : ℕ) (h : primeCore p n = primeCore p m) :
    replaceValuation p n (m.factorization p) = m := by
  unfold replaceValuation
  rw [h]
  exact primeCore_mul_primePower p m

/-- A second resampling of the same prime simply overwrites the first exponent. -/
@[simp] theorem replaceValuation_replaceValuation
    (p n k l : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    replaceValuation p (replaceValuation p n k) l = replaceValuation p n l := by
  change primeCore p (replaceValuation p n k) * p ^ l = primeCore p n * p ^ l
  rw [primeCore_replaceValuation p n k hp hn]

/-- Multiplication by a prime power leaves the prime-free part unchanged. -/
theorem primeCore_pow_mul (p n k : ℕ) (hp : p.Prime) :
    primeCore p (p ^ k * n) = primeCore p n :=
  Nat.ordCompl_self_pow_mul n k hp

theorem primeCore_mul_prime (p m : ℕ) (hp : p.Prime) (_hm : m ≠ 0) :
    primeCore p (p * m) = primeCore p m := by
  simpa only [pow_one] using primeCore_pow_mul p m 1 hp

theorem primeCore_mul (p a b : ℕ) :
    primeCore p (a * b) = primeCore p a * primeCore p b :=
  Nat.ordCompl_mul a b p

theorem primeCore_other_prime (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    primeCore p q = q := by
  apply primeCore_eq_self_of_not_dvd
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)

/-- Resampling p commutes with multiplication by a different prime q. -/
theorem replaceValuation_mul_other_prime (p q n k : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (_hn : n ≠ 0) :
    replaceValuation p (q * n) k = q * replaceValuation p n k := by
  unfold replaceValuation
  rw [primeCore_mul, primeCore_other_prime p q hp hq hpq]
  exact Nat.mul_assoc q (primeCore p n) (p ^ k)

/-- The arithmetic fiber is canonically enumerated by its replacement exponent. -/
def primeFiberEquiv (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    ℕ ≃ {m : ℕ // primeCore p m = primeCore p n} where
  toFun k := ⟨replaceValuation p n k, primeCore_replaceValuation p n k hp hn⟩
  invFun m := m.val.factorization p
  left_inv k := factorization_replaceValuation p n k hp hn
  right_inv m := by
    apply Subtype.ext
    exact replaceValuation_of_primeCore_eq p n m.val m.property.symm

@[simp] theorem primeFiberEquiv_apply_val
    (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) (k : ℕ) :
    (primeFiberEquiv p n hp hn k).val = replaceValuation p n k := rfl

@[simp] theorem primeFiberEquiv_symm_apply
    (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (m : {m : ℕ // primeCore p m = primeCore p n}) :
    (primeFiberEquiv p n hp hn).symm m = m.val.factorization p := rfl

end RiemannResearch.RH.PrimeResampling
