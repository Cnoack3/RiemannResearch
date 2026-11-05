/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogBootstrapFinite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.Bertrand

/-!
# Finite bounds for the ordinary Mertens function by odd pairing

The pairing of an odd integer `m` with `2*m` is described by M. Gabdullin,
*Elementary estimates for the Mertens function*, Illinois Mathematics Lab,
https://iml.math.illinois.edu/files/2025/07/IML-mu-details.pdf. The source
records `x/4 + 3` and `2*x/9 + O(1)`. Below the exact integer endpoints are
kept. Bertrand's postulate supplies opposite Möbius signs on every dyadic
interval considered here once `n ≥ 18`; see P. Erdős, *Beweis eines Satzes
von Tschebyschef*, Acta Litt. ac Sci. Szeged 5 (1932), 194–198,
https://acta.bibl.u-szeged.hu/13396/. This gives the sharp uniform intercept
for slope `2/9`, realized at `x = 5`.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

private abbrev muReal (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ)

/-- Sum of the Möbius values on the first `k` odd positive integers. -/
def oddMertensPrefix (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (ArithmeticFunction.moebius (2 * j + 1) : ℝ)

private theorem oddMertensPrefix_succ (k : ℕ) :
    oddMertensPrefix (k + 1) = oddMertensPrefix k + muReal (2 * k + 1) :=
  Finset.sum_range_succ _ _

private theorem mertens_integer_succ (n : ℕ) :
    M ((n + 1 : ℕ) : ℝ) = M (n : ℝ) + muReal (n + 1) := by
  simp only [M_nat_eq_sum_range, muReal]
  exact Finset.sum_range_succ _ _

private theorem muReal_eq_zero_of_prime_square {p n : ℕ} (hp : p.Prime)
    (hdiv : p * p ∣ n) : muReal n = 0 := by
  have hz : ArithmeticFunction.moebius n = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      (fun hs => (Nat.squarefree_iff_prime_squarefree.mp hs) p hp hdiv)
  simp [muReal, hz]

private theorem muReal_twice_odd (k : ℕ) :
    muReal (2 * (2 * k + 1)) = -muReal (2 * k + 1) := by
  have hc : Nat.Coprime 2 (2 * k + 1) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have he : ArithmeticFunction.moebius (2 * (2 * k + 1)) =
      -ArithmeticFunction.moebius (2 * k + 1) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two, neg_one_mul]
  simp [muReal, he]

/-- The odd terms at most `n/2` cancel their even partners. The two prefix indices
count the odd integers at most `n` and at most `n/2`, respectively. -/
theorem M_nat_eq_oddMertensPrefix_sub (n : ℕ) :
    M (n : ℝ) = oddMertensPrefix ((n + 1) / 2) - oddMertensPrefix ((n + 2) / 4) := by
  induction n with
  | zero =>
    have h : M ((0 : ℕ) : ℝ) = 0 := by rw [M_nat_eq_sum_range]; simp
    simpa [oddMertensPrefix] using h
  | succ n ih =>
    change M ((n + 1 : ℕ) : ℝ) =
      oddMertensPrefix ((n + 1 + 1) / 2) - oddMertensPrefix ((n + 1 + 2) / 4)
    rw [mertens_integer_succ, ih]
    by_cases he : n % 2 = 0
    · have hi : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      have hj : (n + 1 + 2) / 4 = (n + 2) / 4 := by omega
      have hx : 2 * ((n + 1) / 2) + 1 = n + 1 := by omega
      rw [hi, hj, oddMertensPrefix_succ, hx]
      ring
    · have hi : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      by_cases hfour : 4 ∣ n + 1
      · have hj : (n + 1 + 2) / 4 = (n + 2) / 4 := by omega
        have hz : muReal (n + 1) = 0 := muReal_eq_zero_of_prime_square Nat.prime_two hfour
        rw [hi, hj, hz, add_zero]
      · have hj : (n + 1 + 2) / 4 = (n + 2) / 4 + 1 := by omega
        have hx : n + 1 = 2 * (2 * ((n + 2) / 4) + 1) := by omega
        have hz : muReal (n + 1) = -muReal (2 * ((n + 2) / 4) + 1) :=
          (congrArg muReal hx).trans (muReal_twice_odd _)
        rw [hi, hj, oddMertensPrefix_succ, hz]
        ring

/-- After pairing, the Möbius sum is bounded by the actual number of odd squarefree
integers in `(n/2,n]`. This preserves every square divisor in a finite certificate. -/
theorem M_nat_abs_le_odd_squarefree_card (n : ℕ) :
    |M (n : ℝ)| ≤ (((Finset.Ico ((n + 2) / 4) ((n + 1) / 2)).filter
      (fun j => Squarefree (2 * j + 1))).card : ℝ) := by
  classical
  let a := (n + 2) / 4
  let b := (n + 1) / 2
  have hab : a ≤ b := by dsimp [a, b]; omega
  have hsum : M (n : ℝ) = ∑ j ∈ Finset.Ico a b, muReal (2 * j + 1) := by
    rw [M_nat_eq_oddMertensPrefix_sub, Finset.sum_Ico_eq_sub _ hab]
    rfl
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ Finset.Ico a b, |muReal (2 * j + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.Ico a b, (if Squarefree (2 * j + 1) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hs : Squarefree (2 * j + 1)
      · rw [if_pos hs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs)
      · rw [if_neg hs]
        simp [muReal, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    _ = _ := by rw [← Finset.sum_filter]; simp [a, b]

/-- Number of odd indices `0 ≤ j < k` for which `9` does not divide `2*j+1`. -/
def oddNineSieveCount (k : ℕ) : ℕ := k - (k + 4) / 9

private theorem muReal_le_oddNineSieve_step (k : ℕ) :
    |muReal (2 * k + 1)| ≤ (oddNineSieveCount (k + 1) : ℝ) - oddNineSieveCount k := by
  by_cases h : k % 9 = 4
  · have he : oddNineSieveCount (k + 1) = oddNineSieveCount k := by
      unfold oddNineSieveCount
      omega
    have hdiv : 3 * 3 ∣ 2 * k + 1 := ⟨2 * (k / 9) + 1, by omega⟩
    simp [he, muReal_eq_zero_of_prime_square Nat.prime_three hdiv]
  · have he : oddNineSieveCount (k + 1) = oddNineSieveCount k + 1 := by
      unfold oddNineSieveCount
      omega
    have hmu : |muReal (2 * k + 1)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := 2 * k + 1)
    rw [he, Nat.cast_add, Nat.cast_one]
    linarith

private theorem oddMertensPrefix_abs_sub_le {a b : ℕ} (hab : a ≤ b) :
    |oddMertensPrefix b - oddMertensPrefix a| ≤
      (oddNineSieveCount b : ℝ) - oddNineSieveCount a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b _ ih =>
    rw [oddMertensPrefix_succ]
    have hstep := muReal_le_oddNineSieve_step b
    calc
      _ = |(oddMertensPrefix b - oddMertensPrefix a) + muReal (2 * b + 1)| :=
        congrArg abs (by ring)
      _ ≤ |oddMertensPrefix b - oddMertensPrefix a| + |muReal (2 * b + 1)| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- All-integer explicit bound retaining the endpoint dependence modulo 36. -/
theorem M_nat_abs_le_oddNineSieve (n : ℕ) :
    |M (n : ℝ)| ≤ (oddNineSieveCount ((n + 1) / 2) : ℝ) -
      oddNineSieveCount ((n + 2) / 4) := by
  rw [M_nat_eq_oddMertensPrefix_sub]
  exact oddMertensPrefix_abs_sub_le (by omega)

private theorem oddNineSieve_affine (n : ℕ) :
    9 * oddNineSieveCount ((n + 1) / 2) ≤
      2 * n + 13 + 9 * oddNineSieveCount ((n + 2) / 4) := by
  unfold oddNineSieveCount
  have hr : n % 36 < 36 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 36 <;> omega

/-- The additive constant `13/9` is attained by the sieve majorant in the class
`n ≡ 25 (mod 36)`. The assertion concerns the ordinary, unweighted Mertens sum. -/
theorem M_nat_abs_le_two_ninths (n : ℕ) : |M (n : ℝ)| ≤ (2 * (n : ℝ) + 13) / 9 := by
  have ha : (9 : ℝ) * oddNineSieveCount ((n + 1) / 2) ≤
      2 * (n : ℝ) + 13 + 9 * oddNineSieveCount ((n + 2) / 4) := by
    exact_mod_cast oddNineSieve_affine n
  linarith [M_nat_abs_le_oddNineSieve n]

/-- Uniform affine bound for all nonnegative real arguments, with no threshold. -/
theorem M_abs_le_two_ninths {x : ℝ} (hx : 0 ≤ x) : |M x| ≤ (2 * x + 13) / 9 := by
  have he : M x = M (⌊x⌋₊ : ℝ) := by simp [M]
  rw [he]
  linarith [M_nat_abs_le_two_ninths ⌊x⌋₊, Nat.floor_le hx]

/-- Opposite signs in the surviving interval lower the majorant by two.
The two witnesses can be at any positions in the interval. -/
private theorem oddMertensPrefix_abs_sub_le_of_opposite {a b : ℕ}
    (hpos : ∃ i, a ≤ i ∧ i < b ∧ muReal (2 * i + 1) = 1)
    (hneg : ∃ i, a ≤ i ∧ i < b ∧ muReal (2 * i + 1) = -1) :
    |oddMertensPrefix b - oddMertensPrefix a| ≤
      (oddNineSieveCount b : ℝ) - oddNineSieveCount a - 2 := by
  apply abs_le.mpr
  constructor
  · obtain ⟨i, hai, hib, hi⟩ := hpos
    have hlo := (neg_le_abs (oddMertensPrefix i - oddMertensPrefix a)).trans
      (oddMertensPrefix_abs_sub_le hai)
    have hhi := (neg_le_abs (oddMertensPrefix b - oddMertensPrefix (i + 1))).trans
      (oddMertensPrefix_abs_sub_le (show i + 1 ≤ b by omega))
    have hc := muReal_le_oddNineSieve_step i
    rw [hi, abs_one] at hc
    have hs := oddMertensPrefix_succ i
    rw [hi] at hs
    linarith
  · obtain ⟨i, hai, hib, hi⟩ := hneg
    have hlo := (le_abs_self (oddMertensPrefix i - oddMertensPrefix a)).trans
      (oddMertensPrefix_abs_sub_le hai)
    have hhi := (le_abs_self (oddMertensPrefix b - oddMertensPrefix (i + 1))).trans
      (oddMertensPrefix_abs_sub_le (show i + 1 ≤ b by omega))
    have hc := muReal_le_oddNineSieve_step i
    rw [hi, abs_neg, abs_one] at hc
    have hs := oddMertensPrefix_succ i
    rw [hi] at hs
    linarith

/-- Bertrand at `floor(n/2)` supplies a prime; Bertrand at `floor(n/6)`
supplies a prime `q>3` with `3*q` in the same interval `(n/2,n]`. -/
private theorem mertens_odd_interval_opposite (n : ℕ) (hn : 18 ≤ n) :
    (∃ i, (n + 2) / 4 ≤ i ∧ i < (n + 1) / 2 ∧ muReal (2 * i + 1) = 1) ∧
    (∃ i, (n + 2) / 4 ≤ i ∧ i < (n + 1) / 2 ∧ muReal (2 * i + 1) = -1) := by
  constructor
  · obtain ⟨q, hq, hqlo, hqhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 6) (by omega)
    have hq3 : 3 < q := by omega
    obtain ⟨k, hk⟩ := hq.odd_of_ne_two (by omega)
    have hi : 2 * (3 * k + 1) + 1 = 3 * q := by omega
    refine ⟨3 * k + 1, by omega, by omega, ?_⟩
    have hc : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq).mpr (by omega)
    have hmu : ArithmeticFunction.moebius (3 * q) = 1 := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
        ArithmeticFunction.moebius_apply_prime Nat.prime_three,
        ArithmeticFunction.moebius_apply_prime hq] <;> norm_num
    simp [hi, muReal, hmu]
  · obtain ⟨p, hp, hplo, hphi⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    have hi : 2 * k + 1 = p := by omega
    refine ⟨k, by omega, by omega, ?_⟩
    simp [hi, muReal, ArithmeticFunction.moebius_apply_prime hp]

/-- Every integer argument `n ≥ 18` permits two units of additional cancellation. -/
theorem M_nat_abs_le_oddNineSieve_sub_two (n : ℕ) (hn : 18 ≤ n) :
    |M (n : ℝ)| ≤ (oddNineSieveCount ((n + 1) / 2) : ℝ) -
      oddNineSieveCount ((n + 2) / 4) - 2 := by
  obtain ⟨hpos, hneg⟩ := mertens_odd_interval_opposite n hn
  rw [M_nat_eq_oddMertensPrefix_sub]
  exact oddMertensPrefix_abs_sub_le_of_opposite hpos hneg

theorem M_nat_abs_le_two_ninths_sub_five (n : ℕ) (hn : 18 ≤ n) :
    |M (n : ℝ)| ≤ (2 * (n : ℝ) - 5) / 9 := by
  have ha : (9 : ℝ) * oddNineSieveCount ((n + 1) / 2) ≤
      2 * (n : ℝ) + 13 + 9 * oddNineSieveCount ((n + 2) / 4) := by
    exact_mod_cast oddNineSieve_affine n
  linarith [M_nat_abs_le_oddNineSieve_sub_two n hn]

/-- Uniform bound with the optimal intercept for this slope. The only arithmetic
input beyond the exact pairing is Bertrand's postulate, proved in Mathlib. -/
theorem M_nat_abs_le_two_ninths_sharp (n : ℕ) : |M (n : ℝ)| ≤ (2 * (n : ℝ) + 8) / 9 := by
  by_cases hn : 18 ≤ n
  · linarith [M_nat_abs_le_two_ninths_sub_five n hn]
  · have hsmall : n ≤ 17 := by omega
    have ha : 9 * oddNineSieveCount ((n + 1) / 2) ≤
        2 * n + 8 + 9 * oddNineSieveCount ((n + 2) / 4) := by
      interval_cases n <;> decide
    have ha' : (9 : ℝ) * oddNineSieveCount ((n + 1) / 2) ≤
        2 * (n : ℝ) + 8 + 9 * oddNineSieveCount ((n + 2) / 4) := by
      exact_mod_cast ha
    linarith [M_nat_abs_le_oddNineSieve n]

theorem M_abs_le_two_ninths_sub_five {x : ℝ} (hx : 18 ≤ x) : |M x| ≤ (2 * x - 5) / 9 := by
  have hxf : (18 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have he : M x = M (⌊x⌋₊ : ℝ) := by simp [M]
  rw [he]
  linarith [M_nat_abs_le_two_ninths_sub_five ⌊x⌋₊ hxf, Nat.floor_le (show 0 ≤ x by linarith)]

theorem M_abs_le_two_ninths_sharp {x : ℝ} (hx : 0 ≤ x) : |M x| ≤ (2 * x + 8) / 9 := by
  have he : M x = M (⌊x⌋₊ : ℝ) := by simp [M]
  rw [he]
  linarith [M_nat_abs_le_two_ninths_sharp ⌊x⌋₊, Nat.floor_le hx]

private theorem mertens_value_five : M 5 = -2 := by
  change M ((5 : ℕ) : ℝ) = -2
  rw [M_nat_eq_oddMertensPrefix_sub]
  change oddMertensPrefix 3 - oddMertensPrefix 1 = -2
  have h3 := ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h5 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5)
  norm_num [oddMertensPrefix, Finset.sum_range_succ, ArithmeticFunction.moebius_apply_one, h3, h5]

/-- The smallest `c` such that `|M(x)| ≤ (2*x+c)/9` on every nonnegative real
argument is exactly eight. Necessity already follows by evaluating at `x=5`. -/
theorem M_two_ninths_global_intercept_iff (c : ℝ) :
    (∀ x : ℝ, 0 ≤ x → |M x| ≤ (2 * x + c) / 9) ↔ 8 ≤ c := by
  constructor
  · intro h
    have h5 := h 5 (by norm_num)
    rw [mertens_value_five] at h5
    norm_num at h5
    linarith
  · intro hc x hx
    linarith [M_abs_le_two_ninths_sharp hx]

end RiemannResearch.NumberTheory.PrimeNumberTheorem
