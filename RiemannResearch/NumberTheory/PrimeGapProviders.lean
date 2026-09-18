import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Nth
import RiemannResearch.Analysis.GapEnergySummability

/-!
# Actual prime-gap providers and conditional dyadic energy

Unconditional: actual prime enumeration, Bertrand's bound, and total dyadic
gap mass at most 4X. These remove the total-mass premise in the actual-prime
specialization of the cubic energy reduction.

Conditional: the sharp maximal-gap and exceptional-mass estimates are
explicit arguments of the exponent and summability theorems. Neither the
Baker--Harman--Pintz estimate nor Jarviniemi's estimate is proved here.

Provenance:
* Mathlib.NumberTheory.Bertrand supplies a kernel-checked proof of Bertrand's
  postulate, via Nat.exists_prime_lt_and_le_two_mul.
* Source: user-provided gap-energy continuation, Section 12.2, for the
  cubic-energy consumer and the short/long split.
* Baker, Harman and Pintz, "The difference between consecutive primes, II",
  Proc. London Math. Soc. 83 (2001), 532--562,
  https://doi.org/10.1112/plms/83.3.532, supports the intended 21/40
  maximal-gap input, not a Lean proof of that input.
* O. Jarviniemi, "On large differences between consecutive primes",
  https://arxiv.org/html/2212.10965v2, Theorem 1.2, supports the intended
  9/20 threshold and 63/100 + epsilon mass exponent. We choose epsilon
  equal to 1/100, giving 16/25. This citation is not a formal provider.

All estimates concern nonnegative geometric gap energies. No estimate for
the signed von Mangoldt discrepancy or RH is asserted.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimeGapProviders

/-- The zero-based enumeration of all primes. -/
def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Every enumerated value is an actual natural prime. -/
theorem prime_isPrime (n : ℕ) : Nat.Prime (prime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n

/-- The enumeration is strictly increasing. -/
theorem prime_strictMono : StrictMono prime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

/-- A finite numeric bound on a prime also bounds its index. -/
theorem index_le_prime (n : ℕ) : n ≤ prime n :=
  prime_strictMono.id_le n

/-- There is no omitted prime between consecutive enumerated primes. -/
theorem next_prime_le {n q : ℕ} (hq : Nat.Prime q) (hlt : prime n < q) :
    prime (n + 1) ≤ q := by
  obtain ⟨k, hk⟩ := Nat.subset_range_nth hq
  change prime k = q at hk
  have hnk : n < k := prime_strictMono.lt_iff_lt.mp (by simpa [hk] using hlt)
  rw [← hk]
  exact prime_strictMono.monotone (Nat.succ_le_of_lt hnk)

/-- Unconditional Bertrand bound; this is weaker than the BHP estimate. -/
theorem next_prime_le_two_mul (n : ℕ) : prime (n + 1) ≤ 2 * prime n := by
  obtain ⟨q, hq, hlt, hqbound⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (prime n) (prime_isPrime n).ne_zero
  exact (next_prime_le hq hlt).trans hqbound

/-- Actual consecutive-prime gap, viewed in the reals. -/
def gap (n : ℕ) : ℝ := (prime (n + 1) : ℝ) - (prime n : ℝ)

/-- Prime gaps are nonnegative. -/
theorem gap_nonneg (n : ℕ) : 0 ≤ gap n := by
  apply sub_nonneg.mpr
  exact_mod_cast prime_strictMono.monotone (Nat.le_succ n)

/-- Unconditional linear bound for the actual gap. -/
theorem gap_le_prime (n : ℕ) : gap n ≤ (prime n : ℝ) := by
  have h : (prime (n + 1) : ℝ) ≤ 2 * (prime n : ℝ) := by
    exact_mod_cast next_prime_le_two_mul n
  dsimp [gap]
  linarith

/-- All prime indices whose left endpoint lies in the closed dyadic shell. -/
def dyadicIndices (X : ℕ) : Finset ℕ :=
  (Finset.range (2 * X + 1)).filter (fun n => X ≤ prime n ∧ prime n ≤ 2 * X)

/-- The finite cutoff omits no prime in the shell. -/
theorem mem_dyadicIndices {n X : ℕ} :
    n ∈ dyadicIndices X ↔ X ≤ prime n ∧ prime n ≤ 2 * X := by
  simp only [dyadicIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by have := index_le_prime n; omega, h⟩

/-- Unconditional total-gap-mass provider, including the final boundary-crossing gap. -/
theorem dyadic_gap_mass_le (X : ℕ) :
    (∑ n ∈ dyadicIndices X, gap n) ≤ 4 * (X : ℝ) := by
  have hm : Monotone (fun n => (prime n : ℝ)) := by
    intro i j hij
    exact Nat.cast_le.mpr (prime_strictMono.monotone hij)
  apply RiemannResearch.Analysis.GapEnergy.sum_adjacent_gaps_le
    (fun n => (prime n : ℝ)) hm (Nat.cast_nonneg _) (2 * X + 1)
    (dyadicIndices X) (4 * (X : ℝ)) (by positivity)
  · exact Finset.filter_subset _ _
  · intro n hn
    have h := next_prime_le_two_mul n
    have hb := (mem_dyadicIndices.mp hn).2
    have : prime (n + 1) ≤ 4 * X := by omega
    exact_mod_cast this

/-- Conditional cubic bound for actual primes: total mass is proved, while the
maximal-gap and exceptional-mass estimates remain explicit hypotheses. -/
theorem dyadic_cubic_gap_le (X : ℕ) (H G L : ℝ)
    (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hmax : ∀ n ∈ dyadicIndices X, gap n ≤ G)
    (hlarge : (∑ n ∈ (dyadicIndices X).filter (fun n => H ≤ gap n), gap n) ≤ L) :
    (∑ n ∈ dyadicIndices X, gap n ^ 3) ≤
      H ^ 2 * (4 * (X : ℝ)) + G ^ 2 * L :=
  RiemannResearch.Analysis.GapEnergy.cubic_gap_sum_le_of_external_bounds
    (dyadicIndices X) gap H G (4 * (X : ℝ)) L hH hG
    (fun n _ => gap_nonneg n) hmax (dyadic_gap_mass_le X) hlarge

/-- Exact exponent assembly from the BHP-sized maximal gap and the
Jarviniemi-sized exceptional mass with epsilon = 1/100. This does not prove either input. -/
theorem dyadic_cubic_gap_le_published_exponents (X : ℕ) (hX : 0 < X)
    (C D : ℝ) (hC : 0 ≤ C)
    (hmax : ∀ n ∈ dyadicIndices X, gap n ≤ C * (X : ℝ) ^ (21 / 40 : ℝ))
    (hlarge : (∑ n ∈ (dyadicIndices X).filter
      (fun n => (X : ℝ) ^ (9 / 20 : ℝ) ≤ gap n), gap n) ≤
        D * (X : ℝ) ^ (16 / 25 : ℝ)) :
    (∑ n ∈ dyadicIndices X, gap n ^ 3) ≤
      4 * (X : ℝ) ^ (19 / 10 : ℝ) +
        C ^ 2 * D * (X : ℝ) ^ (169 / 100 : ℝ) := by
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have hs : ((X : ℝ) ^ (9 / 20 : ℝ)) ^ 2 * (4 * (X : ℝ)) =
      4 * (X : ℝ) ^ (19 / 10 : ℝ) := by
    calc
      _ = 4 * (((X : ℝ) ^ (9 / 20 : ℝ) * (X : ℝ) ^ (9 / 20 : ℝ)) *
          (X : ℝ) ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by
        rw [← Real.rpow_add hx, ← Real.rpow_add hx]
        norm_num
  have hl : (C * (X : ℝ) ^ (21 / 40 : ℝ)) ^ 2 *
      (D * (X : ℝ) ^ (16 / 25 : ℝ)) =
        C ^ 2 * D * (X : ℝ) ^ (169 / 100 : ℝ) := by
    calc
      _ = C ^ 2 * D * (((X : ℝ) ^ (21 / 40 : ℝ) *
          (X : ℝ) ^ (21 / 40 : ℝ)) * (X : ℝ) ^ (16 / 25 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hx, ← Real.rpow_add hx]
        norm_num
  have h := dyadic_cubic_gap_le X ((X : ℝ) ^ (9 / 20 : ℝ))
    (C * (X : ℝ) ^ (21 / 40 : ℝ)) (D * (X : ℝ) ^ (16 / 25 : ℝ))
    (Real.rpow_nonneg hx.le _) (mul_nonneg hC (Real.rpow_nonneg hx.le _))
    hmax hlarge
  simpa only [hs, hl] using h

/-- The two input estimates give decay exponents -1/10 and -31/100 after normalization. -/
theorem dyadic_normalized_cubic_le (X : ℕ) (hX : 0 < X)
    (C D : ℝ) (hC : 0 ≤ C)
    (hmax : ∀ n ∈ dyadicIndices X, gap n ≤ C * (X : ℝ) ^ (21 / 40 : ℝ))
    (hlarge : (∑ n ∈ (dyadicIndices X).filter
      (fun n => (X : ℝ) ^ (9 / 20 : ℝ) ≤ gap n), gap n) ≤
        D * (X : ℝ) ^ (16 / 25 : ℝ)) :
    (∑ n ∈ dyadicIndices X, gap n ^ 3) / (X : ℝ) ^ 2 ≤
      4 * (X : ℝ) ^ (-1 / 10 : ℝ) +
        C ^ 2 * D * (X : ℝ) ^ (-31 / 100 : ℝ) := by
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have hs : (X : ℝ) ^ (19 / 10 : ℝ) / (X : ℝ) ^ 2 =
      (X : ℝ) ^ (-1 / 10 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hx]
    norm_num
  have hl : (X : ℝ) ^ (169 / 100 : ℝ) / (X : ℝ) ^ 2 =
      (X : ℝ) ^ (-31 / 100 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hx]
    norm_num
  have h := div_le_div_of_nonneg_right
    (dyadic_cubic_gap_le_published_exponents X hX C D hC hmax hlarge)
    (sq_nonneg (X : ℝ))
  simpa only [add_div, mul_div_assoc, hs, hl] using h

/-- Conditional summability for actual dyadic prime-gap energies. The two
arithmetic bounds hmax and hlarge are still hypotheses, not established providers. -/
theorem summable_dyadic_normalized_cubic_of_gap_bounds (C D : ℝ) (hC : 0 ≤ C)
    (hmax : ∀ k n, n ∈ dyadicIndices (2 ^ k) →
      gap n ≤ C * ((2 ^ k : ℕ) : ℝ) ^ (21 / 40 : ℝ))
    (hlarge : ∀ k, (∑ n ∈ (dyadicIndices (2 ^ k)).filter
      (fun n => ((2 ^ k : ℕ) : ℝ) ^ (9 / 20 : ℝ) ≤ gap n), gap n) ≤
        D * ((2 ^ k : ℕ) : ℝ) ^ (16 / 25 : ℝ)) :
    Summable (fun k : ℕ =>
      (∑ n ∈ dyadicIndices (2 ^ k), gap n ^ 3) / ((2 ^ k : ℕ) : ℝ) ^ 2) := by
  have hp (e : ℝ) (he : e < 0) :
      Summable (fun k : ℕ => ((2 ^ k : ℕ) : ℝ) ^ e) := by
    have hid (k : ℕ) : ((2 : ℝ) ^ k) ^ e = ((2 : ℝ) ^ e) ^ k := by
      rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have hs := summable_geometric_of_lt_one
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) e)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) he)
    simpa only [Nat.cast_pow, Nat.cast_ofNat, hid] using hs
  have hs := ((hp (-1 / 10) (by norm_num)).mul_left 4).add
    ((hp (-31 / 100) (by norm_num)).mul_left (C ^ 2 * D))
  apply Summable.of_nonneg_of_le _ _ hs
  · intro k
    exact div_nonneg (Finset.sum_nonneg (fun n _ => pow_nonneg (gap_nonneg n) 3))
      (sq_nonneg _)
  · intro k
    exact dyadic_normalized_cubic_le (2 ^ k) (pow_pos (by norm_num) _)
      C D hC (hmax k) (hlarge k)

end RiemannResearch.NumberTheory.PrimeGapProviders
