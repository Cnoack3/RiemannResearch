/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.PrimeTreePairedChains
import RiemannResearch.RH.PrimeTreeCarryLaw
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-! # The actual positive-inverse chain on consecutive primes

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§§3 and 5.1. Each local lift is the representative in [1,D); its integer
partner is the negative Euclidean quotient. Bertrand's theorem supplies
an elementary bound for the next radix after the exceptional initial edge.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CanonicalPrimeCarry
open CRTCarryArithmetic PrimeTreeTwoCarry

def primeAt (k : ℕ) : ℕ := Nat.nth Nat.Prime k
def radix (k : ℕ) : ℕ := primeAt (k+1)
def primorialAt (k : ℕ) : ℕ := ∏ j ∈ Finset.range (k+1), primeAt j

theorem primeAt_prime (k : ℕ) : (primeAt k).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k

private theorem primeAt_strictMono : StrictMono primeAt :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

private theorem prefix_zero : primorialAt 0 = 2 := by simp [primorialAt, primeAt]
private theorem radix_zero : radix 0 = 3 := Nat.nth_prime_one_eq_three
private theorem prefix_succ (k : ℕ) : primorialAt (k+1) = primorialAt k * radix k :=
  Finset.prod_range_succ _ _

private theorem prefix_two_le (k : ℕ) : 2 ≤ primorialAt k := by
  induction k with
  | zero => simp [prefix_zero]
  | succ k ih =>
    rw [prefix_succ]
    exact ih.trans (Nat.le_mul_of_pos_right _ (primeAt_prime (k+1)).pos)

private theorem radix_coprime (k : ℕ) : (radix k).Coprime (primorialAt k) := by
  apply (primeAt_prime (k+1)).coprime_iff_not_dvd.mpr
  intro h
  obtain ⟨j, hj, hjp⟩ := ((primeAt_prime (k+1)).prime.dvd_finsetProd_iff _).mp h
  have he := (Nat.prime_dvd_prime_iff_eq (primeAt_prime (k+1)) (primeAt_prime j)).mp hjp
  exact (primeAt_strictMono (Finset.mem_range.mp hj)).ne he.symm

/-- Every incoming prime after the first edge fits inside its parent modulus. -/
theorem radix_le_prefix (k : ℕ) : radix (k+1) ≤ primorialAt (k+1) := by
  obtain ⟨q, hq, hgt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (radix k)
    (primeAt_prime (k+1)).ne_zero
  have hn : radix (k+1) ≤ q := by
    by_contra! h
    exact hgt.not_ge (Nat.le_nth_of_lt_nth_succ h hq)
  rw [prefix_succ]
  exact hn.trans (hle.trans (Nat.mul_le_mul_right _ (prefix_two_le k)))

private theorem inverse_exists (k : ℕ) :
    ∃ u : ℕ, u < primorialAt k ∧ radix k * u % primorialAt k = 1 :=
  Nat.exists_mul_mod_eq_one_of_coprime (radix_coprime k) (prefix_two_le k)

def positiveInverse (k : ℕ) : ℕ := Nat.find (inverse_exists k)

theorem inverse_spec (k : ℕ) :
    positiveInverse k < primorialAt k ∧ radix k * positiveInverse k % primorialAt k = 1 :=
  Nat.find_spec (inverse_exists k)

private theorem inverse_pos (k : ℕ) : 0 < positiveInverse k := by
  by_contra! he
  have hz : positiveInverse k = 0 := by omega
  simpa [hz] using (inverse_spec k).2

theorem inverse_zero : positiveInverse 0 = 1 := by
  have hu := (inverse_spec 0).1
  rw [prefix_zero] at hu
  have hp := inverse_pos 0
  omega

theorem inverse_after_first (k : ℕ) : 2 ≤ positiveInverse (k+1) := by
  have hlt : radix (k+1) < primorialAt (k+1) := by
    refine lt_of_le_of_ne (radix_le_prefix k) ?_
    intro he
    have hd := radix_coprime (k+1)
    rw [he] at hd
    have h1 : primorialAt (k+1) = 1 := by simpa [Nat.Coprime] using hd
    have := prefix_two_le (k+1)
    omega
  by_contra! h
  have hi := inverse_pos (k+1)
  have ho : positiveInverse (k+1) = 1 := by omega
  have he := (inverse_spec (k+1)).2
  rw [ho, Nat.mul_one, Nat.mod_eq_of_lt hlt] at he
  exact (primeAt_prime (k+1+1)).ne_one he

def carryPartner (k : ℕ) : ℤ := -((radix k * positiveInverse k / primorialAt k : ℕ) : ℤ)

theorem inverse_bezout (k : ℕ) :
    ((positiveInverse k : ℕ) : ℝ) * (radix k : ℝ) + (carryPartner k : ℝ) * (primorialAt k : ℝ) = 1 := by
  have he := Nat.mod_add_div (radix k * positiveInverse k) (primorialAt k)
  rw [(inverse_spec k).2] at he
  have h := congrArg (fun x : ℕ => (x : ℝ)) he
  push_cast at h
  simp only [carryPartner, Int.cast_neg, Int.cast_natCast]
  linarith only [h, mul_comm (radix k : ℝ) (positiveInverse k : ℝ),
    mul_comm ((radix k * positiveInverse k / primorialAt k : ℕ) : ℝ) (primorialAt k : ℝ)]

def weight : ℕ → ℝ
  | 0 => 1
  | k+1 => weight k / (positiveInverse k : ℝ)

theorem weight_pos (k : ℕ) : 0 < weight k := by
  induction k with
  | zero => norm_num [weight]
  | succ k ih => exact div_pos ih (Nat.cast_pos.mpr (inverse_pos k))

theorem weight_antitone_step (k : ℕ) : weight (k+1) ≤ weight k := by
  apply div_le_self (weight_pos k).le
  exact_mod_cast inverse_pos k

private theorem weight_le_one (k : ℕ) : weight k ≤ 1 := by
  induction k with
  | zero => simp [weight]
  | succ k ih => exact (weight_antitone_step k).trans ih

def firstChain : NormalizedCarryChain where
  D := primorialAt
  p := radix
  a := fun k => (positiveInverse k : ℤ)
  b := carryPartner
  w := weight
  start_pos := by rw [prefix_zero]; decide
  radix_ge := fun k => (primeAt_prime (k+1)).two_le
  next := prefix_succ
  bezout := fun k => by simpa using inverse_bezout k
  normalize := by
    intro k
    change (weight k / (positiveInverse k : ℝ)) * (((positiveInverse k : ℕ) : ℤ) : ℝ) = weight k
    push_cast
    exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (inverse_pos k).ne')
  weight_bound := fun k => by rw [abs_of_pos (weight_pos k)]; exact weight_le_one k

def thirdChain : NormalizedCarryChain :=
  firstChain.changeFirstToThree prefix_zero radix_zero (by change (positiveInverse 0 : ℤ) = 1; simp [inverse_zero])
    (by rfl)

/-- Formula (21) for the literal prime chain and floor carries, with no
chain existence, summability, transform, or path hypotheses. -/
theorem first_third_readout_zero_iff (s : ℂ) (hs : 0 < s.re) (h1 : s.re < 1) :
    (readout firstChain.chainSignal s = 0 ∧ readout thirdChain.chainSignal s = 0) ↔
      riemannZeta s = 0 := by
  have ha : firstChain.a 0 = 1 := by
    change (positiveInverse 0 : ℤ) = 1
    simp [inverse_zero]
  have hi (k : ℕ) : (2 : ℤ) ≤ firstChain.a (k+1) := by
    change (2 : ℤ) ≤ (positiveInverse (k+1) : ℤ)
    exact_mod_cast inverse_after_first k
  exact firstChain.paired_chain_zero_iff prefix_zero radix_zero ha (by rfl)
    (fun k => (weight_pos k).le) hi radix_le_prefix s hs h1

/-- Formula (8) for the explicit positive-inverse probability. -/
theorem firstChain_probability : HasSum firstChain.edgeMass 1 ∧ ∀ k, 0 < firstChain.edgeMass k :=
  ⟨firstChain.edgeMass_total prefix_zero rfl,
    firstChain.edgeMass_pos weight_pos weight_antitone_step⟩

end RiemannResearch.RH.CanonicalPrimeCarry
