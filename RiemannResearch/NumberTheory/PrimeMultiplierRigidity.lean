/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic rigidity of prime-atom multipliers

Source: user-provided paper proof, final operator-algebra section, 4 November 2026.
The argument only uses three prime residue tests at each site and holds over any
characteristic-zero field. Boundedness, Hilbert norm assumptions, and RH are not
required. The intended RH consumer is QSquarefreeMultiplierRigidity.
-/

namespace RiemannResearch.NumberTheory.PrimeMultiplierRigidity

theorem previous_mod_of_dvd (p n : ℕ) (hp : 2 ≤ p) (hn : 1 ≤ n)
    (hpn : p ∣ n) : (n - 1) % p = p - 1 := by
  have hstep : n % p = ((n - 1) % p + 1) % p := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [Nat.add_mod]
    simp only [Nat.mod_eq_of_lt (by omega : 1 < p)]
  have hz : n % p = 0 := Nat.mod_eq_zero_of_dvd hpn
  have hr : (n - 1) % p < p := Nat.mod_lt _ (by omega)
  by_contra hne
  have hlt : (n - 1) % p + 1 < p := by omega
  rw [Nat.mod_eq_of_lt hlt] at hstep
  omega

variable {K : Type*} [Field K] [CharZero K]

/-- Only three prime tests per site are needed; no boundedness or topology. -/
theorem adjacent_eq_of_prime_tests (h : ℕ → K)
    (htest : ∀ p : ℕ, p.Prime → ∀ n : ℕ, 2 ≤ n →
      h (n-1) * ((n-1) % p : ℕ) - h n * (n % p : ℕ) -
        h (n^2-1) * ((n^2-1) % p : ℕ) + h (n^2) * (n^2 % p : ℕ) = 0)
    (n : ℕ) (hn : 3 ≤ n) : h n = h (n-1) := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hpn2 : p ∣ n^2 := by
    simpa only [pow_two] using dvd_mul_of_dvd_left hpn n
  have hn2 : 1 ≤ n^2 := by nlinarith
  have hP := htest p hp n (by omega)
  rw [previous_mod_of_dvd p n hp.two_le (by omega) hpn,
    previous_mod_of_dvd p (n^2) hp.two_le hn2 hpn2,
    Nat.mod_eq_zero_of_dvd hpn, Nat.mod_eq_zero_of_dvd hpn2] at hP
  simp only [Nat.cast_zero, mul_zero, sub_zero, add_zero] at hP
  have hpne : ((p-1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast (show p-1 ≠ 0 by have := hp.two_le; omega)
  have heprev : h (n-1) = h (n^2-1) :=
    mul_right_cancel₀ hpne (sub_eq_zero.mp hP)
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (show n-1 ≠ 1 by omega)
  have he : n = (n-1)+1 := by omega
  have hnmod : n % q = 1 := by
    conv_lhs => rw [he]
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hqn]
    simp [Nat.mod_eq_of_lt hq.one_lt]
  have hn2mod : n^2 % q = 1 := by rw [Nat.pow_mod, hnmod]; simp [Nat.mod_eq_of_lt hq.one_lt]
  have hfactor : n^2-1 = (n-1)*(n+1) := by
    have hsub := Nat.sub_add_cancel (show 1 ≤ n by omega)
    have hsub2 := Nat.sub_add_cancel hn2
    nlinarith
  have hqn2 : q ∣ n^2-1 := by
    rw [hfactor]
    exact dvd_mul_of_dvd_left hqn (n+1)
  have hQ := htest q hq n (by omega)
  rw [Nat.mod_eq_zero_of_dvd hqn, Nat.mod_eq_zero_of_dvd hqn2,
    hnmod, hn2mod] at hQ
  simp only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, zero_sub, sub_zero] at hQ
  have hecurr : h (n^2) = h n := by linear_combination hQ
  obtain ⟨l, hl, hlp⟩ := Nat.exists_infinite_primes (n^2+1)
  have hnn : n < l := by nlinarith
  have hL := htest l hlp n (by omega)
  rw [Nat.mod_eq_of_lt (show n-1 < l by omega),
    Nat.mod_eq_of_lt hnn,
    Nat.mod_eq_of_lt (show n^2-1 < l by omega),
    Nat.mod_eq_of_lt (show n^2 < l by omega),
    ← heprev, hecurr,
    Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub hn2,
    Nat.cast_one, Nat.cast_pow] at hL
  have hz : ((n : K) * ((n : K)-1)) * (h n - h (n-1)) = 0 := by
    linear_combination hL
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : K)-1 ≠ 0 := by
    have hnat : ((n-1 : ℕ) : K) ≠ 0 := by exact_mod_cast (show n-1 ≠ 0 by omega)
    simpa only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] using hnat
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hn0 hn1))


/-- Constant on every positive physical integer over any characteristic-zero field. -/
theorem constant_of_prime_tests (h : ℕ → K)
    (htest : ∀ p : ℕ, p.Prime → ∀ n : ℕ, 2 ≤ n →
      h (n-1) * ((n-1) % p : ℕ) - h n * (n % p : ℕ) -
        h (n^2-1) * ((n^2-1) % p : ℕ) + h (n^2) * (n^2 % p : ℕ) = 0) :
    ∀ n : ℕ, 1 ≤ n → h n = h 1 := by
  have h13 := htest 2 Nat.prime_two 2 (by decide)
  norm_num at h13
  have h32 := adjacent_eq_of_prime_tests h htest 3 (by decide)
  norm_num at h32
  have h21 : h 2 = h 1 := by linear_combination -h13 - h32
  have htail : ∀ k : ℕ, h (k+2) = h 2 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hh := adjacent_eq_of_prime_tests h htest (k+3) (by omega)
        have he : k+3-1 = k+2 := by omega
        rw [he] at hh
        exact hh.trans ih
  intro n hn
  by_cases he : n = 1
  · simp only [he]
  · have hn2 : 2 ≤ n := by omega
    have hh := htail (n-2)
    rw [Nat.sub_add_cancel hn2] at hh
    exact hh.trans h21

end RiemannResearch.NumberTheory.PrimeMultiplierRigidity
