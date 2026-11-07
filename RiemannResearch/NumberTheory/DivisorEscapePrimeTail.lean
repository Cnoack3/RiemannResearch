/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.DivisorEscapeEulerProduct
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Complete LCM Euler tails with a logarithmic saving

The user's CRT collocation handoff identifies the complete divisor-escape tail
as the arithmetic input to the Mellin annihilator estimate. This module retains
both the size and depth contributions: every prime above the cutoff contributes
its first power, and every smaller prime contributes its first forbidden power.

The prime-counting input is the checked Mathlib Chebyshev machinery:
`Chebyshev.eventually_primeCounting_le` and
`Chebyshev.pi_le_log4_mul_div`. The dyadic cover and all prime-power comparisons
are proved here. No prime number theorem, RH hypothesis, or tail-rate provider is
assumed.

Main results:
* `primeEscape_lcmUpto_split`: exact small-prime depth / large-prime size split.
* `eventually_tail_lcmUpto_le_log`: the eventual Chebyshev constant.
* `tail_lcmUpto_le_explicit_log`: a fully explicit bound for every cutoff M ≥ 2.
* `tail_lcmUpto_le_min_explicit`: combine the integral and Euler upper bounds.
* `small_prime_depth_le_split` and `small_prime_depth_square_le`: a finer depth bound.
* `tail_lcmUpto_lower_explicit`: a matching lower bound from Chebyshev prime counts.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.DivisorEscapeTail

/-- Primes up to a natural cutoff, with their primality certificates retained. -/
def primePrefix (M : ℕ) : Finset Nat.Primes := (Nat.primesLE M).subtype Nat.Prime

@[simp] theorem mem_primePrefix (M : ℕ) (p : Nat.Primes) :
    p ∈ primePrefix M ↔ (p : ℕ) ≤ M := by
  change (⟨(p : ℕ), p.property⟩ : Subtype Nat.Prime) ∈
    (Nat.primesLE M).subtype Nat.Prime ↔ (p : ℕ) ≤ M
  exact Finset.mem_subtype.trans
    ⟨fun h => (Nat.mem_primesLE.mp h).1, fun h => Nat.mem_primesLE.mpr ⟨h, p.property⟩⟩

@[simp] theorem card_primePrefix (M : ℕ) :
    (primePrefix M).card = M.primeCounting := by
  have hm : (primePrefix M).map (Function.Embedding.subtype Nat.Prime) = M.primesLE :=
    Finset.subtype_map_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  change ((M.primesLE).subtype Nat.Prime).card = M.primeCounting
  calc
    _ = (((M.primesLE).subtype Nat.Prime).map
        (Function.Embedding.subtype Nat.Prime)).card := (Finset.card_map _).symm
    _ = M.primesLE.card := congrArg Finset.card hm
    _ = M.primeCounting := Nat.primesLE_card_eq_primeCounting M

/-- The first forbidden prime power lies strictly beyond the LCM cutoff. -/
theorem cutoff_lt_first_escape_power (M : ℕ) (p : Nat.Primes) :
    M < (p : ℕ)^((Nat.lcmUpto M).factorization p + 1) := by
  rw [Nat.factorization_lcmUpto M p.property]
  exact Nat.lt_pow_succ_log_self p.property.one_lt M

/-- The depth contribution of every prime is at most the cutoff weight.
This retains the full first forbidden power, including small primes. -/
theorem primeEscape_lcmUpto_le_cutoff (t : ℝ) (ht : 1 < t)
    (M : ℕ) (hM : 0 < M) (p : Nat.Primes) :
    primeEscape t (Nat.lcmUpto M) p ≤ (M : ℝ)^(-t) := by
  rw [primeEscape, ← nat_pow_rpow]
  apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hM)
    (by exact_mod_cast (cutoff_lt_first_escape_power M p).le)
    (by linarith)

/-- Above the cutoff the first forbidden power is the prime itself. -/
theorem primeEscape_lcmUpto_eq_power (t : ℝ) (M : ℕ) (p : Nat.Primes)
    (hMp : M < (p : ℕ)) :
    primeEscape t (Nat.lcmUpto M) p = ((p : ℕ) : ℝ)^(-t) := by
  simp only [primeEscape, Nat.factorization_lcmUpto M p.property,
    Nat.log_of_lt hMp, zero_add, pow_one]

/-- The complete tail over primes larger than a cutoff. -/
def primeTail (t : ℝ) (M : ℕ) : ℝ :=
  ∑' p : Nat.Primes, if M < (p : ℕ) then ((p : ℕ) : ℝ)^(-t) else 0

theorem summable_primeTail (t : ℝ) (ht : 1 < t) (M : ℕ) :
    Summable (fun p : Nat.Primes =>
      if M < (p : ℕ) then ((p : ℕ) : ℝ)^(-t) else 0) := by
  apply Summable.of_nonneg_of_le
    (fun p : Nat.Primes => by split_ifs <;> positivity)
    (fun p : Nat.Primes => show (if M < (p : ℕ) then ((p : ℕ) : ℝ)^(-t) else 0) ≤
      ((p : ℕ) : ℝ)^(-t) from by
        split_ifs
        · exact le_rfl
        · exact Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact (Real.summable_nat_rpow.mpr (by linarith : -t < -1)).comp_injective
    Subtype.val_injective

/-- Exact separation of small-prime depth and large-prime size escape. -/
theorem primeEscape_lcmUpto_split (t : ℝ) (ht : 1 < t) (M : ℕ) :
    (∑' p : Nat.Primes, primeEscape t (Nat.lcmUpto M) p) =
      (∑ p ∈ primePrefix M, primeEscape t (Nat.lcmUpto M) p) + primeTail t M := by
  classical
  let h : Nat.Primes → ℝ := fun p =>
    if p ∈ primePrefix M then primeEscape t (Nat.lcmUpto M) p else 0
  have hs : Summable h := by
    apply summable_of_ne_finset_zero (s := primePrefix M)
    intro p hp
    simp only [h, if_neg hp]
  have hsum : (∑' p : Nat.Primes, h p) =
      ∑ p ∈ primePrefix M, primeEscape t (Nat.lcmUpto M) p := by
    rw [tsum_eq_sum (s := primePrefix M) (by intro p hp; simp only [h, if_neg hp])]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [h, if_pos hp]
  calc
    _ = ∑' p : Nat.Primes, (h p +
        if M < (p : ℕ) then ((p : ℕ) : ℝ)^(-t) else 0) := by
      apply tsum_congr
      intro p
      by_cases hp : (p : ℕ) ≤ M
      · simp only [h, mem_primePrefix, if_pos hp, if_neg (not_lt.mpr hp), add_zero]
      · have hMp := Nat.lt_of_not_ge hp
        simp only [h, mem_primePrefix, if_neg hp, if_pos hMp, zero_add,
          primeEscape_lcmUpto_eq_power t M p hMp]
    _ = _ := by rw [hs.tsum_add (summable_primeTail t ht M), hsum]; rfl

/-- A finite, explicitly computable depth bound; no prime powers are dropped. -/
theorem small_prime_depth_le_count (t : ℝ) (ht : 1 < t) (M : ℕ) (hM : 0 < M) :
    (∑ p ∈ primePrefix M, primeEscape t (Nat.lcmUpto M) p) ≤
      (M.primeCounting : ℝ) * (M : ℝ)^(-t) := by
  calc
    _ ≤ ∑ p ∈ primePrefix M, (M : ℝ)^(-t) :=
      Finset.sum_le_sum (fun p _ => primeEscape_lcmUpto_le_cutoff t ht M hM p)
    _ = _ := by simp only [Finset.sum_const, card_primePrefix, nsmul_eq_mul]

/-- Euler escape is bounded by a finite small-prime depth term plus a genuine
prime tail. This decomposition is stronger than replacing every integer by escape. -/
theorem tail_lcmUpto_le_depth_add_primeTail (t : ℝ) (ht : 1 < t)
    (M : ℕ) (hM : 0 < M) :
    tail t (Nat.lcmUpto M) ≤ (∑' n : ℕ, (n : ℝ)^(-t)) *
      ((M.primeCounting : ℝ) * (M : ℝ)^(-t) + primeTail t M) := by
  apply (tail_le_series_mul_prime_escape t ht _ (Nat.lcmUpto_pos M)).trans
  apply mul_le_mul_of_nonneg_left _ (power_series_pos t ht).le
  rw [primeEscape_lcmUpto_split t ht M]
  exact add_le_add (small_prime_depth_le_count t ht M hM) le_rfl

/-- Chebyshev already supplies a logarithmic saving for the complete finite
small-prime depth contribution. -/
theorem eventually_small_prime_depth_le (t : ℝ) (ht : 1 < t)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      (∑ p ∈ primePrefix M, primeEscape t (Nat.lcmUpto M) p) ≤
        (Real.log 4 + ε) * (M : ℝ)^(1-t) / Real.log M := by
  have hc := (tendsto_natCast_atTop_atTop :
    Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop).eventually
      (Chebyshev.eventually_primeCounting_le hε)
  filter_upwards [hc, eventually_ge_atTop (1 : ℕ)] with M hc hM
  have hM0 : 0 < M := by omega
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM0
  have hc' : (M.primeCounting : ℝ) ≤
      (Real.log 4 + ε) * (M : ℝ) / Real.log M := by
    simpa only [Nat.floor_natCast] using hc
  calc
    _ ≤ (M.primeCounting : ℝ) * (M : ℝ)^(-t) :=
      small_prime_depth_le_count t ht M hM0
    _ ≤ ((Real.log 4 + ε) * (M : ℝ) / Real.log M) * (M : ℝ)^(-t) :=
      mul_le_mul_of_nonneg_right hc' (Real.rpow_nonneg hMr.le _)
    _ = _ := by
      rw [show 1-t = 1+(-t) by ring, Real.rpow_add hMr, Real.rpow_one]
      ring

/-- Every integer beyond a positive cutoff lies in a dyadic interval. -/
theorem exists_dyadic_cover (M n : ℕ) (hM : 0 < M) (hMn : M < n) :
    ∃ j : ℕ, 2^j * M ≤ n ∧ n ≤ 2^(j+1) * M := by
  let j := Nat.log 2 (n / M)
  have hq : 0 < n / M := Nat.div_pos hMn.le hM
  have hl : 2^j ≤ n / M := Nat.pow_log_le_self 2 (Nat.ne_of_gt hq)
  refine ⟨j, (Nat.mul_le_mul_right M hl).trans (Nat.div_mul_le_self n M), ?_⟩
  exact ((Nat.div_lt_iff_lt_mul hM).mp
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n / M))).le

/-- A geometric dyadic majorant for prime counts yields a bound for the
actual prime tail. The cover may overlap, so no primes are lost. -/
theorem primeTail_le_of_dyadic_count (t : ℝ) (ht : 1 < t)
    (M : ℕ) (hM : 0 < M) (A q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcount : ∀ j : ℕ,
      ((2^(j+1)*M).primeCounting : ℝ) * (((2^j*M : ℕ) : ℝ)^(-t)) ≤ A*q^j) :
    primeTail t M ≤ A / (1-q) := by
  classical
  let b : ℕ → Nat.Primes → ℝ := fun j p =>
    if (p : ℕ) ≤ 2^(j+1)*M then (((2^j*M : ℕ) : ℝ)^(-t)) else 0
  have hb (j : ℕ) (p : Nat.Primes) : 0 ≤ b j p := by
    dsimp only [b]
    split_ifs <;> positivity
  have hs (j : ℕ) : Summable (b j) := by
    apply summable_of_ne_finset_zero (s := primePrefix (2^(j+1)*M))
    intro p hp
    have hp' : ¬ (p : ℕ) ≤ 2^(j+1)*M := by simpa only [mem_primePrefix] using hp
    simp only [b, if_neg hp']
  have he (j : ℕ) : (∑' p : Nat.Primes, b j p) =
      ((2^(j+1)*M).primeCounting : ℝ) * (((2^j*M : ℕ) : ℝ)^(-t)) := by
    rw [tsum_eq_sum (s := primePrefix (2^(j+1)*M)) (by
      intro p hp
      have hp' : ¬ (p : ℕ) ≤ 2^(j+1)*M := by simpa only [mem_primePrefix] using hp
      simp only [b, if_neg hp'])]
    calc
      _ = ∑ p ∈ primePrefix (2^(j+1)*M), (((2^j*M : ℕ) : ℝ)^(-t)) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [b, if_pos ((mem_primePrefix _ p).mp hp)]
      _ = _ := by simp only [Finset.sum_const, card_primePrefix, nsmul_eq_mul]
  have hgeom : Summable (fun j : ℕ => A*q^j) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left A
  have houter : Summable (fun j : ℕ => ∑' p : Nat.Primes, b j p) := by
    apply Summable.of_nonneg_of_le (fun j => tsum_nonneg (hb j)) _ hgeom
    intro j
    rw [he]
    exact hcount j
  have hpair : Summable (Function.uncurry b) :=
    (summable_prod_of_nonneg (fun jp => hb jp.1 jp.2)).mpr ⟨hs, houter⟩
  have hmajor (p : Nat.Primes) :
      (if M < (p : ℕ) then ((p : ℕ) : ℝ)^(-t) else 0) ≤ ∑' j : ℕ, b j p := by
    split_ifs with hp
    · obtain ⟨j, hjlo, hjhi⟩ := exists_dyadic_cover M p hM hp
      have hweight : ((p : ℕ) : ℝ)^(-t) ≤ (((2^j*M : ℕ) : ℝ)^(-t)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hjlo) (by linarith)
      have hj : b j p ≤ ∑' k : ℕ, b k p := by
        have hs' : Summable (fun k : ℕ => b k p) := hpair.prod_symm.prod_factor p
        simpa only [Finset.sum_singleton] using
          sum_le_hasSum ({j} : Finset ℕ) (fun k _ => hb k p) hs'.hasSum
      exact hweight.trans (by simpa only [b, if_pos hjhi] using hj)
    · exact tsum_nonneg (fun j => hb j p)
  calc
    primeTail t M ≤ ∑' p : Nat.Primes, ∑' j : ℕ, b j p :=
      Summable.tsum_le_tsum hmajor (summable_primeTail t ht M) hpair.prod_symm.prod
    _ = ∑' j : ℕ, ∑' p : Nat.Primes, b j p := hpair.tsum_comm
    _ ≤ ∑' j : ℕ, A*q^j :=
      Summable.tsum_le_tsum (fun j => (he j).symm ▸ hcount j) houter hgeom
    _ = A / (1-q) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

/-- The power and counting factors of a dyadic interval form a geometric series. -/
theorem dyadic_weight_identity (t C : ℝ) (M j : ℕ) (hM : 0 < M) :
    (C * ((2^(j+1)*M : ℕ) : ℝ) / Real.log M) *
      (((2^j*M : ℕ) : ℝ)^(-t)) =
      (2*C*(M : ℝ)^(1-t)/Real.log M) * ((2 : ℝ)^(1-t))^j := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have h2 : (2 : ℝ)^(1-t) = 2*(2 : ℝ)^(-t) := by
    rw [show 1-t = 1+(-t) by ring, Real.rpow_add (by norm_num : 0 < (2 : ℝ)),
      Real.rpow_one]
  have hm : (M : ℝ)^(1-t) = (M : ℝ)*(M : ℝ)^(-t) := by
    rw [show 1-t = 1+(-t) by ring, Real.rpow_add hMr, Real.rpow_one]
  simp only [Nat.cast_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg M),
    nat_pow_rpow, h2, hm, mul_pow]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  ring

/-- A uniform Chebyshev bound above M gives a logarithmically improved prime tail. -/
theorem primeTail_le_of_primeCounting (t : ℝ) (ht : 1 < t) (M : ℕ)
    (hM : 1 < M) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, M ≤ N →
      (N.primeCounting : ℝ) ≤ C*(N : ℝ)/Real.log N) :
    primeTail t M ≤
      (2*C*(M : ℝ)^(1-t)/Real.log M) / (1-(2 : ℝ)^(1-t)) := by
  have hM0 : 0 < M := by omega
  have hMr : 1 < (M : ℝ) := by exact_mod_cast hM
  apply primeTail_le_of_dyadic_count t ht M hM0 _ _
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  intro j
  have hj1 : 1 ≤ (2 : ℕ)^(j+1) := by
    have hp : 0 < (2 : ℕ)^(j+1) := pow_pos (by decide) _
    omega
  have hMN : M ≤ 2^(j+1)*M := by
    simpa only [one_mul] using Nat.mul_le_mul_right M hj1
  have hMNreal : (M : ℝ) ≤ ((2^(j+1)*M : ℕ) : ℝ) := by exact_mod_cast hMN
  have hlog : Real.log M ≤ Real.log ((2^(j+1)*M : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hMNreal
  calc
    _ ≤ (C * ((2^(j+1)*M : ℕ) : ℝ) /
          Real.log ((2^(j+1)*M : ℕ) : ℝ)) * (((2^j*M : ℕ) : ℝ)^(-t)) :=
      mul_le_mul_of_nonneg_right (hcount _ hMN) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ (C * ((2^(j+1)*M : ℕ) : ℝ) / Real.log M) *
          (((2^j*M : ℕ) : ℝ)^(-t)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      exact div_le_div_of_nonneg_left (mul_nonneg hC (Nat.cast_nonneg _))
        (Real.log_pos hMr) hlog
    _ = _ := dyadic_weight_identity t C M j hM0

/-- The complete prime tail has an unconditional logarithmic saving, using only
Mathlib's Chebyshev bound, not the prime number theorem. -/
theorem eventually_primeTail_le (t : ℝ) (ht : 1 < t) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      primeTail t M ≤
        (2*(Real.log 4+ε)*(M : ℝ)^(1-t)/Real.log M) /
          (1-(2 : ℝ)^(1-t)) := by
  have hc := (tendsto_natCast_atTop_atTop :
    Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop).eventually
      (Chebyshev.eventually_primeCounting_le hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  filter_upwards [eventually_ge_atTop (max N 2)] with M hM
  apply primeTail_le_of_primeCounting t ht M (by omega) (Real.log 4+ε)
    (by positivity)
  intro K hMK
  simpa only [Nat.floor_natCast] using hN K (le_trans (le_max_left N 2) (hM.trans hMK))

/-- The full LCM Euler tail, including every prime-power depth, improves the
integer-tail rate by a logarithmic factor. -/
theorem eventually_tail_lcmUpto_le_log (t : ℝ) (ht : 1 < t) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      tail t (Nat.lcmUpto M) ≤
        (∑' n : ℕ, (n : ℝ)^(-t)) * (Real.log 4+ε) *
          (1 + 2/(1-(2 : ℝ)^(1-t))) * (M : ℝ)^(1-t) / Real.log M := by
  filter_upwards [eventually_small_prime_depth_le t ht ε hε,
    eventually_primeTail_le t ht ε hε] with M hdepth hprime
  apply (tail_le_series_mul_prime_escape t ht _ (Nat.lcmUpto_pos M)).trans
  rw [primeEscape_lcmUpto_split t ht M]
  calc
    _ ≤ (∑' n : ℕ, (n : ℝ)^(-t)) *
        ((Real.log 4+ε)*(M : ℝ)^(1-t)/Real.log M +
        (2*(Real.log 4+ε)*(M : ℝ)^(1-t)/Real.log M)/(1-(2 : ℝ)^(1-t))) :=
      mul_le_mul_of_nonneg_left (add_le_add hdepth hprime) (power_series_pos t ht).le
    _ = _ := by ring

/-- A prime already included in the LCM can escape only at exponent at least two. -/
theorem primeEscape_lcmUpto_le_square (t : ℝ) (ht : 1 < t) (M : ℕ)
    (p : Nat.Primes) (hpM : (p : ℕ) ≤ M) :
    primeEscape t (Nat.lcmUpto M) p ≤ ((p : ℕ) : ℝ)^(-(2*t)) := by
  have hq0 : 0 ≤ ((p : ℕ) : ℝ)^(-t) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hq1 : ((p : ℕ) : ℝ)^(-t) ≤ 1 :=
    (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (by linarith : -t < 0)).le
  have hv : 1 ≤ (Nat.lcmUpto M).factorization p := by
    rw [Nat.factorization_lcmUpto M p.property]
    exact Nat.le_log_of_pow_le p.property.one_lt (by simpa only [pow_one] using hpM)
  have he : (Nat.lcmUpto M).factorization p + 1 =
      2 + ((Nat.lcmUpto M).factorization p - 1) := by omega
  have hpow : primeEscape t (Nat.lcmUpto M) p ≤ (((p : ℕ) : ℝ)^(-t))^2 := by
    rw [primeEscape, he, pow_add]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1)
        (sq_nonneg (((p : ℕ) : ℝ)^(-t)))
  apply hpow.trans_eq
  rw [pow_two, ← Real.rpow_add (by exact_mod_cast p.property.pos)]
  congr 1
  ring

/-- A second cutoff separates the shallow and deep small-prime terms. Choosing
K near sqrt(M) improves the finite depth contribution by an additional square-root scale. -/
theorem small_prime_depth_le_split (t : ℝ) (ht : 1 < t) (M K : ℕ) (hM : 0 < M) :
    (∑ p ∈ primePrefix M, primeEscape t (Nat.lcmUpto M) p) ≤
      (K.primeCounting : ℝ) * (M : ℝ)^(-t) + primeTail (2*t) K := by
  classical
  let a : Nat.Primes → ℝ := fun p => if (p : ℕ) ≤ K then (M : ℝ)^(-t) else 0
  let b : Nat.Primes → ℝ := fun p =>
    if K < (p : ℕ) then ((p : ℕ) : ℝ)^(-(2*t)) else 0
  have ha0 (p : Nat.Primes) : 0 ≤ a p := by dsimp only [a]; split_ifs <;> positivity
  have hb0 (p : Nat.Primes) : 0 ≤ b p := by dsimp only [b]; split_ifs <;> positivity
  have ha : Summable a := by
    apply summable_of_ne_finset_zero (s := primePrefix K)
    intro p hp
    have hp' : ¬ (p : ℕ) ≤ K := by simpa only [mem_primePrefix] using hp
    simp only [a, if_neg hp']
  have hat : (∑' p : Nat.Primes, a p) = (K.primeCounting : ℝ)*(M : ℝ)^(-t) := by
    rw [tsum_eq_sum (s := primePrefix K) (by
      intro p hp
      have hp' : ¬ (p : ℕ) ≤ K := by simpa only [mem_primePrefix] using hp
      simp only [a, if_neg hp'])]
    calc
      _ = ∑ p ∈ primePrefix K, (M : ℝ)^(-t) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [a, if_pos ((mem_primePrefix K p).mp hp)]
      _ = _ := by simp only [Finset.sum_const, card_primePrefix, nsmul_eq_mul]
  have hb : Summable b := summable_primeTail (2*t) (by linarith) K
  calc
    _ ≤ ∑ p ∈ primePrefix M, (a p+b p) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpK : (p : ℕ) ≤ K
      · simp only [a, b, if_pos hpK, if_neg (not_lt.mpr hpK), add_zero]
        exact primeEscape_lcmUpto_le_cutoff t ht M hM p
      · simp only [a, b, if_neg hpK, if_pos (Nat.lt_of_not_ge hpK), zero_add]
        exact primeEscape_lcmUpto_le_square t ht M p ((mem_primePrefix M p).mp hp)
    _ ≤ ∑' p : Nat.Primes, (a p+b p) :=
      sum_le_hasSum (primePrefix M) (fun p _ => add_nonneg (ha0 p) (hb0 p))
        (ha.add hb).hasSum
    _ = _ := by rw [ha.tsum_add hb, hat]; rfl

/-- Explicit square-depth refinement under a uniform prime-counting bound. -/
theorem small_prime_depth_le_split_counting (t : ℝ) (ht : 1 < t)
    (M K : ℕ) (hM : 0 < M) (hK : 1 < K) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, K ≤ N →
      (N.primeCounting : ℝ) ≤ C*(N : ℝ)/Real.log N) :
    (∑ p ∈ primePrefix M, primeEscape t (Nat.lcmUpto M) p) ≤
      (K.primeCounting : ℝ) * (M : ℝ)^(-t) +
        (2*C*(K : ℝ)^(1-2*t)/Real.log K)/(1-(2 : ℝ)^(1-2*t)) := by
  apply (small_prime_depth_le_split t ht M K hM).trans
  exact add_le_add le_rfl (primeTail_le_of_primeCounting (2*t) (by linarith) K hK C hC hcount)

/-- A deliberately simple uniform Chebyshev constant, valid from M=2 onward. -/
theorem primeCounting_le_explicit (M : ℕ) (hM : 1 < M) :
    (M.primeCounting : ℝ) ≤ (2*Real.log 4+2)*(M : ℝ)/Real.log M := by
  have hMr : 1 < (M : ℝ) := by exact_mod_cast hM
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hlogpos : 0 < Real.log (M : ℝ) := Real.log_pos hMr
  have hlogsqrt := Real.log_le_self (Real.sqrt_nonneg (M : ℝ))
  rw [Real.log_sqrt hM0] at hlogsqrt
  have hl : Real.log (M : ℝ) ≤ 2*Real.sqrt (M : ℝ) := by linarith
  have hsqrt : Real.sqrt (M : ℝ) ≤ 2*(M : ℝ)/Real.log M := by
    apply (le_div_iff₀ hlogpos).mpr
    have hm := mul_le_mul_of_nonneg_right hl (Real.sqrt_nonneg (M : ℝ))
    nlinarith [Real.sq_sqrt hM0]
  calc
    (M.primeCounting : ℝ) ≤
        Real.log 4*(M : ℝ)/Real.log (Real.sqrt (M : ℝ)) + Real.sqrt (M : ℝ) := by
      simpa only [Nat.floor_natCast] using Chebyshev.pi_le_log4_mul_div hMr
    _ = 2*Real.log 4*(M : ℝ)/Real.log M + Real.sqrt (M : ℝ) := by
      rw [Real.log_sqrt hM0]
      ring
    _ ≤ 2*Real.log 4*(M : ℝ)/Real.log M + 2*(M : ℝ)/Real.log M :=
      add_le_add le_rfl hsqrt
    _ = _ := by ring

/-- Fully explicit logarithmically improved LCM Euler-tail bound, valid for
every M≥2. All small-prime depth and large-prime escape are included. -/
theorem tail_lcmUpto_le_explicit_log (t : ℝ) (ht : 1 < t)
    (M : ℕ) (hM : 1 < M) :
    tail t (Nat.lcmUpto M) ≤
      (∑' n : ℕ, (n : ℝ)^(-t)) * (2*Real.log 4+2) *
        (1+2/(1-(2 : ℝ)^(1-t))) * (M : ℝ)^(1-t)/Real.log M := by
  have hM0 : 0 < M := by omega
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM0
  let C : ℝ := 2*Real.log 4+2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hdepth : (∑ p ∈ primePrefix M, primeEscape t (Nat.lcmUpto M) p) ≤
      C*(M : ℝ)^(1-t)/Real.log M := by
    calc
      _ ≤ (M.primeCounting : ℝ)*(M : ℝ)^(-t) :=
        small_prime_depth_le_count t ht M hM0
      _ ≤ (C*(M : ℝ)/Real.log M)*(M : ℝ)^(-t) :=
        mul_le_mul_of_nonneg_right (primeCounting_le_explicit M hM)
          (Real.rpow_nonneg hMr.le _)
      _ = _ := by
        rw [show 1-t = 1+(-t) by ring, Real.rpow_add hMr, Real.rpow_one]
        ring
  have hprime : primeTail t M ≤
      (2*C*(M : ℝ)^(1-t)/Real.log M)/(1-(2 : ℝ)^(1-t)) :=
    primeTail_le_of_primeCounting t ht M hM C hC
      (fun N hMN => primeCounting_le_explicit N (hM.trans_le hMN))
  apply (tail_le_series_mul_prime_escape t ht _ (Nat.lcmUpto_pos M)).trans
  rw [primeEscape_lcmUpto_split t ht M]
  calc
    _ ≤ (∑' n : ℕ, (n : ℝ)^(-t)) *
        (C*(M : ℝ)^(1-t)/Real.log M +
          (2*C*(M : ℝ)^(1-t)/Real.log M)/(1-(2 : ℝ)^(1-t))) :=
      mul_le_mul_of_nonneg_left (add_le_add hdepth hprime) (power_series_pos t ht).le
    _ = _ := by dsimp only [C]; ring

/-- Use the sharper of the direct integral cutoff and the explicit Euler bound. -/
theorem tail_lcmUpto_le_min_explicit (t : ℝ) (ht : 1 < t)
    (M : ℕ) (hM : 1 < M) :
    tail t (Nat.lcmUpto M) ≤ min ((M : ℝ)^(1-t)/(t-1))
      ((∑' n : ℕ, (n : ℝ)^(-t)) * (2*Real.log 4+2) *
        (1+2/(1-(2 : ℝ)^(1-t))) * (M : ℝ)^(1-t)/Real.log M) :=
  le_min (tail_lcmUpto_le t ht M (by omega))
    (tail_lcmUpto_le_explicit_log t ht M hM)

/-- At square cutoffs, the full small-prime depth contribution is on the
smaller scale K^(1-2t)/log K, rather than K^(2-2t)/log K. -/
theorem small_prime_depth_square_le (t : ℝ) (ht : 1 < t) (K : ℕ) (hK : 1 < K) :
    (∑ p ∈ primePrefix (K^2), primeEscape t (Nat.lcmUpto (K^2)) p) ≤
      (2*Real.log 4+2) * (1+2/(1-(2 : ℝ)^(1-2*t))) *
        (K : ℝ)^(1-2*t)/Real.log K := by
  have hK0 : 0 < K := by omega
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK0
  let C : ℝ := 2*Real.log 4+2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hpow : ((K^2 : ℕ) : ℝ)^(-t) = (K : ℝ)^(-(2*t)) := by
    rw [nat_pow_rpow, pow_two, ← Real.rpow_add hKr]
    congr 1
    ring
  have hhead : (K.primeCounting : ℝ)*((K^2 : ℕ) : ℝ)^(-t) ≤
      C*(K : ℝ)^(1-2*t)/Real.log K := by
    rw [hpow]
    calc
      _ ≤ (C*(K : ℝ)/Real.log K)*(K : ℝ)^(-(2*t)) :=
        mul_le_mul_of_nonneg_right (primeCounting_le_explicit K hK)
          (Real.rpow_nonneg hKr.le _)
      _ = _ := by
        rw [show 1-2*t = 1+(-(2*t)) by ring, Real.rpow_add hKr, Real.rpow_one]
        ring
  have hprime : primeTail (2*t) K ≤
      (2*C*(K : ℝ)^(1-2*t)/Real.log K)/(1-(2 : ℝ)^(1-2*t)) :=
    primeTail_le_of_primeCounting (2*t) (by linarith) K hK C hC
      (fun N hKN => primeCounting_le_explicit N (hK.trans_le hKN))
  apply (small_prime_depth_le_split t ht (K^2) K (pow_pos hK0 _)).trans
  calc
    _ ≤ C*(K : ℝ)^(1-2*t)/Real.log K +
        (2*C*(K : ℝ)^(1-2*t)/Real.log K)/(1-(2 : ℝ)^(1-2*t)) :=
      add_le_add hhead hprime
    _ = _ := by dsimp only [C]; ring

/-- The square-cutoff Euler tail separates the dominant prime-size term
from the faster-decaying complete small-prime depth term. -/
theorem tail_lcmUpto_square_le_explicit (t : ℝ) (ht : 1 < t) (K : ℕ) (hK : 1 < K) :
    tail t (Nat.lcmUpto (K^2)) ≤ (∑' n : ℕ, (n : ℝ)^(-t)) *
      ((2*(2*Real.log 4+2)*((K^2 : ℕ) : ℝ)^(1-t)/Real.log (K^2)) /
          (1-(2 : ℝ)^(1-t)) +
        (2*Real.log 4+2)*(1+2/(1-(2 : ℝ)^(1-2*t))) *
          (K : ℝ)^(1-2*t)/Real.log K) := by
  have hKK : 1 < K^2 := by nlinarith
  have hprime := primeTail_le_of_primeCounting t ht (K^2) hKK (2*Real.log 4+2)
    (by positivity) (fun N hKN => primeCounting_le_explicit N (hKK.trans_le hKN))
  have hdepth := small_prime_depth_square_le t ht K hK
  apply (tail_le_series_mul_prime_escape t ht _ (Nat.lcmUpto_pos (K^2))).trans
  rw [primeEscape_lcmUpto_split t ht (K^2)]
  rw [add_comm]
  simpa only [Nat.cast_pow] using
    mul_le_mul_of_nonneg_left (add_le_add hprime hdepth) (power_series_pos t ht).le


/-- A prime interval supplies a lower bound for the complete divisor-escape tail. -/
theorem prime_interval_count_le_tail (t : ℝ) (ht : 1 < t)
    (M N : ℕ) (hMN : M ≤ N) :
    ((N.primeCounting : ℝ)-(M.primeCounting : ℝ))*(N : ℝ)^(-t) ≤
      tail t (Nat.lcmUpto M) := by
  classical
  let S : Finset ℕ := N.primesLE \ M.primesLE
  have hsub : M.primesLE ⊆ N.primesLE := by
    intro p hp
    rcases Nat.mem_primesLE.mp hp with ⟨hpM, hpprime⟩
    exact Nat.mem_primesLE.mpr ⟨hpM.trans hMN, hpprime⟩
  have hcount : M.primeCounting ≤ N.primeCounting := by
    simpa only [Nat.primesLE_card_eq_primeCounting] using Finset.card_le_card hsub
  have hcard : S.card = N.primeCounting-M.primeCounting := by
    dsimp only [S]
    rw [Finset.card_sdiff_of_subset hsub,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hterm (p : ℕ) (hp : p ∈ S) : (N : ℝ)^(-t) ≤ term t (Nat.lcmUpto M) p := by
    rcases Finset.mem_sdiff.mp hp with ⟨hpN, hpM⟩
    rcases Nat.mem_primesLE.mp hpN with ⟨hpN, hpprime⟩
    have hMp : M < p := by
      by_contra h
      exact hpM (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt h, hpprime⟩)
    have hpnot : ¬ p ∣ Nat.lcmUpto M := by
      intro hd
      have hv : 1 ≤ (Nat.lcmUpto M).factorization p :=
        (hpprime.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero M)).mp
          (by simpa only [pow_one] using hd)
      rw [Nat.factorization_lcmUpto M hpprime, Nat.log_of_lt hMp] at hv
      omega
    rw [term, if_neg hpnot]
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hpprime.pos)
      (by exact_mod_cast hpN) (by linarith)
  calc
    _ = (S.card : ℝ)*(N : ℝ)^(-t) := by rw [hcard, Nat.cast_sub hcount]
    _ = ∑ p ∈ S, (N : ℝ)^(-t) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ S, term t (Nat.lcmUpto M) p := Finset.sum_le_sum hterm
    _ ≤ tail t (Nat.lcmUpto M) :=
      sum_le_hasSum S (fun p _ => term_nonneg t _ p) (summable_term t ht _).hasSum

/-- Chebyshev's bounds force a positive supply of primes in (M,32M]. -/
theorem prime_interval_count_lower (M : ℕ) (hM : 32 ≤ M) :
    (4 : ℝ)*(M : ℝ)/Real.log M ≤
      ((32*M).primeCounting : ℝ)-(M.primeCounting : ℝ) := by
  have hMr : 1 < (M : ℝ) := by exact_mod_cast (show 1 < M by omega)
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hMr
  have hlogN : 0 < Real.log ((32*M : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 32*M by omega))
  have hlog4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ)^2 by norm_num, Real.log_pow]
    norm_num
  have hlog2 := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
  norm_num at hlog2
  have hlog32 : Real.log (32 : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have hlogNM : Real.log ((32*M : ℕ) : ℝ) ≤ 2*Real.log (M : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (ne_of_gt (by linarith : 0 < (M : ℝ)))]
    linarith
  have hlow := (div_le_iff₀ hlogN).mp (Chebyshev.pi_ge (32*M))
  have hNr : (2 : ℝ) ≤ ((32*M : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ 32*M by omega)
  have hcorr : Real.log (((32*M : ℕ) : ℝ)+1) ≤
      2*Real.log ((32*M : ℕ) : ℝ) := by
    have hsq : ((32*M : ℕ) : ℝ)+1 ≤ (((32*M : ℕ) : ℝ))^2 := by nlinarith
    have h := Real.log_le_log (by linarith : 0 < ((32*M : ℕ) : ℝ)+1) hsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hmul := mul_le_mul_of_nonneg_left hlogNM
    (by positivity : (0 : ℝ) ≤ ((32*M).primeCounting : ℝ)+2)
  have hupp := (le_div_iff₀ hlogM).mp
    (primeCounting_le_explicit M (by omega))
  rw [hlog4] at hupp
  have hlog2M := mul_le_mul_of_nonneg_right hlog2 (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hlogself : Real.log (M : ℝ) ≤ (M : ℝ) := Real.log_le_self (Nat.cast_nonneg M)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlow hmul hcorr
  apply (div_le_iff₀ hlogM).mpr
  nlinarith

/-- The explicit complete Euler-tail rate is sharp in order for every fixed t>1.
This lower bound uses only the checked Mathlib Chebyshev inequalities. -/
theorem tail_lcmUpto_lower_explicit (t : ℝ) (ht : 1 < t)
    (M : ℕ) (hM : 32 ≤ M) :
    (4 : ℝ)*(32 : ℝ)^(-t)*(M : ℝ)^(1-t)/Real.log M ≤
      tail t (Nat.lcmUpto M) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  calc
    _ = ((4 : ℝ)*(M : ℝ)/Real.log M)*((32*M : ℕ) : ℝ)^(-t) := by
      rw [Nat.cast_mul, Nat.cast_ofNat,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) (Nat.cast_nonneg M),
        show 1-t = 1+(-t) by ring, Real.rpow_add hMr, Real.rpow_one]
      ring
    _ ≤ (((32*M).primeCounting : ℝ)-(M.primeCounting : ℝ))*
        ((32*M : ℕ) : ℝ)^(-t) :=
      mul_le_mul_of_nonneg_right (prime_interval_count_lower M hM)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := prime_interval_count_le_tail t ht M (32*M) (by omega)

end RiemannResearch.NumberTheory.DivisorEscapeTail
