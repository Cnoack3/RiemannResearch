/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FinitePrimeModeArithmetic
import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.PoissonHaarSpecialization
import Mathlib.Analysis.Real.Sqrt

/-!
# Arithmetic support and values of the prime-torus FMZ coefficients

Unique factorization forces the actual rational Landau coefficient to vanish
on mixed prime modes. Single-prime modes have the exact inverse-square-root
Poisson coefficient, for both signs.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.PrimePhaseTorus
open RiemannResearch.Analysis.ActualZeroOrdinate
open RiemannResearch.Analysis.ZeroOrdinate

@[simp] theorem primeNumerator_neg (P : Finset ℕ) (k : ℕ → ℤ) :
    primeNumerator P (fun p => -k p) = primeDenominator P k := rfl

@[simp] theorem primeDenominator_neg (P : Finset ℕ) (k : ℕ → ℤ) :
    primeDenominator P (fun p => -k p) = primeNumerator P k := by
  simp [primeDenominator, primeNumerator]

theorem rationalFMZMain_symm (n m : ℕ) :
    rationalFMZMain n m = rationalFMZMain m n := by
  rcases lt_trichotomy n m with h | h | h
  · simp [rationalFMZMain, h, Nat.not_lt_of_ge h.le]
  · subst m; simp [rationalFMZMain]
  · simp [rationalFMZMain, h, Nat.not_lt_of_ge h.le]

private theorem sqrt_nat_pow (p r : ℕ) :
    Real.sqrt ((p : ℝ) ^ r) = (Real.sqrt (p : ℝ)) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg p) r), ih,
      pow_succ]

theorem rationalFMZMain_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    rationalFMZMain (p ^ r) 1 =
      -(Real.log p / (2 * Real.pi) : ℂ) *
        (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) ^ r := by
  have hpow : IsPrimePow (p ^ r) := ⟨p, r, hp.prime, hr, rfl⟩
  have hlt : 1 < p ^ r := hpow.one_lt
  rw [rationalFMZMain, if_pos hlt,
    rationalLandauMain_eq_vonMangoldt_div_sqrt (by norm_num) hlt]
  simp only [one_dvd, if_true, Nat.div_one, Nat.cast_one, div_one]
  rw [ArithmeticFunction.vonMangoldt_apply_pow hr.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast
  rw [sqrt_nat_pow]
  push_cast
  simp only [div_eq_mul_inv, mul_inv, inv_pow, map_mul, map_inv₀, map_pow]
  ring

theorem rationalFMZMain_eq_zero_of_no_prime_power
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hNM : ¬(m ∣ n ∧ IsPrimePow (n / m)))
    (hMN : ¬(n ∣ m ∧ IsPrimePow (m / n))) :
    rationalFMZMain n m = 0 := by
  unfold rationalFMZMain
  split_ifs with hmn hnm
  · rw [rationalLandauMain_eq_vonMangoldt_div_sqrt hm hmn]
    by_cases hdiv : m ∣ n
    · rw [if_pos hdiv,
        (ArithmeticFunction.vonMangoldt_eq_zero_iff).mpr
          (fun hpow => hNM ⟨hdiv, hpow⟩)]
      simp
    · simp [hdiv]
  · rw [rationalLandauMain_eq_vonMangoldt_div_sqrt hn hnm]
    by_cases hdiv : n ∣ m
    · rw [if_pos hdiv,
        (ArithmeticFunction.vonMangoldt_eq_zero_iff).mpr
          (fun hpow => hMN ⟨hdiv, hpow⟩)]
      simp
    · simp [hdiv]
  · rfl

private theorem not_positivePrimeAxis_of_two_nonzero
    (P : Finset ℕ) (k : ℕ → ℤ) {p q : ℕ}
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (hkp : k p ≠ 0) (hkq : k q ≠ 0) : ¬PositivePrimeAxis P k := by
  rintro ⟨r, hr, hkr, hzero⟩
  by_cases hrp : r = p
  · subst r
    exact hkq (hzero q hq (Ne.symm hpq))
  · exact hkp (hzero p hp (Ne.symm hrp))

theorem rationalFMZMain_prime_eq_zero_of_two_nonzero
    (P : Finset ℕ) (k : ℕ → ℤ) (hP : ∀ p ∈ P, p.Prime)
    {p q : ℕ} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (hkp : k p ≠ 0) (hkq : k q ≠ 0) :
    rationalFMZMain (primeNumerator P k) (primeDenominator P k) = 0 := by
  apply rationalFMZMain_eq_zero_of_no_prime_power
    (primeNumerator P k) (primeDenominator P k)
    (primeProduct_pos P _ hP) (primeProduct_pos P _ hP)
  · rw [prime_integer_prime_power_iff_positive_axis P k hP]
    exact not_positivePrimeAxis_of_two_nonzero P k hp hq hpq hkp hkq
  · have h := not_positivePrimeAxis_of_two_nonzero P (fun r => -k r)
      hp hq hpq (by simpa using hkp) (by simpa using hkq)
    simpa only [primeNumerator_neg, primeDenominator_neg] using
      (mt (prime_integer_prime_power_iff_positive_axis P
        (fun r => -k r) hP).mp h)

theorem rationalFMZMain_prime_single_axis
    (P : Finset ℕ) (k : ℕ → ℤ) (hP : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hp : p ∈ P) (hkp : k p ≠ 0)
    (hzero : ∀ q ∈ P, q ≠ p → k q = 0) :
    rationalFMZMain (primeNumerator P k) (primeDenominator P k) =
      -(Real.log p / (2 * Real.pi) : ℂ) *
        (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) ^ (k p).natAbs := by
  have hN : primeNumerator P k = p ^ (k p).toNat := by
    apply primeProduct_eq_single P _ hp
    intro q hq hqp
    simp [hzero q hq hqp]
  have hD : primeDenominator P k = p ^ (-k p).toNat := by
    apply primeProduct_eq_single P _ hp
    intro q hq hqp
    simp [hzero q hq hqp]
  have habs : 0 < (k p).natAbs := by
    exact Nat.pos_of_ne_zero (by simpa using hkp)
  by_cases hpos : 0 < k p
  · have hto : (k p).toNat = (k p).natAbs := by
      have h := Int.natAbs_of_nonneg hpos.le
      omega
    have hneg : (-k p).toNat = 0 := by omega
    rw [hN, hD, hto, hneg, pow_zero]
    exact rationalFMZMain_prime_pow (hP p hp) habs
  · have hnegpos : 0 < -k p := by omega
    have hto : (-k p).toNat = (k p).natAbs := by
      have h := Int.natAbs_of_nonneg hnegpos.le
      rw [Int.natAbs_neg] at h
      omega
    have hzeroToNat : (k p).toNat = 0 := by omega
    rw [hN, hD, hto, hzeroToNat, pow_zero, rationalFMZMain_symm]
    exact rationalFMZMain_prime_pow (hP p hp) habs

end RiemannResearch.Analysis.PrimePhaseTorus
