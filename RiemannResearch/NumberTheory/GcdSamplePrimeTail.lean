/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.GcdWindowMoments
import RiemannResearch.NumberTheory.GcdSampleTail
import RiemannResearch.NumberTheory.DivisorEscapePrimeTail
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Complete gcd-sampler tails from prime-power escape

Source: user-provided CRT_Collocation_and_Zero_Growth_2026-11-06,
Section 7, and CRTCollocationStabilityResearch20261107, Section 6.
These support the sampler question and the reciprocal-cutoff estimate.
The proof below uses a direct union over first forbidden prime powers:
if p^(v_p(L)+1) divides n, then p*gcd(n,L) divides n.
The exact prime-budget split retains both finite depth and the full prime tail.

The actual sum sampleTail is never replaced by a finite physical truncation.
Main consequences are its O(1/M) bound, its negligible ratio to the complete
escape tail for 1<t<2, and the sharper auxiliary-threshold/square-cutoff estimate.
No canonical-lift norm bound or RH hypothesis is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.DivisorEscapeTail

def samplePrimeWeight (t : ℝ) (L : ℕ) (p : Nat.Primes) : ℝ :=
  ((p : ℕ) : ℝ)^(t-2) * primeEscape t L p

theorem samplePrimeWeight_nonneg (t : ℝ) (L : ℕ) (p : Nat.Primes) :
    0 ≤ samplePrimeWeight t L p :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (primeEscape_nonneg t L p)

theorem samplePrimeWeight_le_rpow_neg_two (t : ℝ) (ht : 1 < t)
    (L : ℕ) (p : Nat.Primes) :
    samplePrimeWeight t L p ≤ ((p : ℕ) : ℝ)^(- (2 : ℝ)) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  calc
    _ ≤ ((p : ℕ) : ℝ)^(t-2) * ((p : ℕ) : ℝ)^(-t) :=
      mul_le_mul_of_nonneg_left (primeEscape_le_power t ht L p)
        (Real.rpow_nonneg hp.le _)
    _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring

theorem samplePrimeWeight_summable (t : ℝ) (ht : 1 < t) (L : ℕ) :
    Summable (samplePrimeWeight t L) := by
  have hs : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ)^(-(2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(2 : ℝ) < -1)).comp_injective
      Subtype.val_injective
  exact Summable.of_nonneg_of_le (samplePrimeWeight_nonneg t L)
    (samplePrimeWeight_le_rpow_neg_two t ht L) hs

theorem exists_prime_escape_of_not_dvd (L n : ℕ) (hL : 0 < L)
    (hn : 0 < n) (hnL : ¬ n ∣ L) :
    ∃ p : Nat.Primes, (p : ℕ) ^ (L.factorization p + 1) ∣ n := by
  by_contra h
  apply hnL
  apply (Nat.factorization_le_iff_dvd (ne_of_gt hn) (ne_of_gt hL)).mp
  intro p
  by_cases hp : p.Prime
  · by_contra hp'
    have he : L.factorization p + 1 ≤ n.factorization p := by omega
    exact h ⟨⟨p, hp⟩, (hp.pow_dvd_iff_le_factorization (ne_of_gt hn)).mpr he⟩
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp, le_refl]

theorem escape_prime_mul_gcd_dvd (L n : ℕ) (hL : 0 < L) (hn : 0 < n)
    (p : Nat.Primes) (hp : (p : ℕ) ^ (L.factorization p + 1) ∣ n) :
    (p : ℕ) * Nat.gcd n L ∣ n := by
  have hg : Nat.gcd n L ≠ 0 := ne_of_gt (Nat.gcd_pos_of_pos_left L hn)
  apply (Nat.factorization_le_iff_dvd
    (mul_ne_zero p.property.ne_zero hg) (ne_of_gt hn)).mp
  rw [Nat.factorization_mul p.property.ne_zero hg,
    Nat.factorization_gcd (ne_of_gt hn) (ne_of_gt hL)]
  intro q
  have he : L.factorization p + 1 ≤ n.factorization p :=
    (p.property.pow_dvd_iff_le_factorization (ne_of_gt hn)).mp hp
  by_cases hq : q = (p : ℕ)
  · subst q
    simp only [Finsupp.add_apply, Nat.Prime.factorization p.property,
      Finsupp.single_eq_same, Finsupp.inf_apply]
    omega
  · simp only [Finsupp.add_apply, Nat.Prime.factorization p.property,
      Finsupp.single_eq_of_ne hq, Finsupp.inf_apply, zero_add]
    exact min_le_left _ _

theorem sampleTerm_le_prime_cover (t : ℝ) (ht2 : t ≤ 2)
    (L n : ℕ) (hL : 0 < L) (hn : 0 < n) (p : Nat.Primes)
    (hp : (p : ℕ) ^ (L.factorization p + 1) ∣ n) :
    sampleTerm t L n ≤ ((p : ℕ) : ℝ)^(t-2) * (n : ℝ)^(-t) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  have hgn : ((p : ℕ) : ℝ) * (Nat.gcd n L : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd hn (escape_prime_mul_gcd_dvd L n hL hn p hp)
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ ((p : ℕ) : ℝ) *
      (Nat.gcd n L : ℝ)) hgn (sub_nonneg.mpr ht2)
  rw [Real.mul_rpow hpR.le (Nat.cast_nonneg _)] at hpow
  have hcancel : ((p : ℕ) : ℝ)^(t-2) * ((p : ℕ) : ℝ)^(2-t) = 1 := by
    rw [← Real.rpow_add hpR]; simp
  have hg : (Nat.gcd n L : ℝ)^(2-t) ≤
      ((p : ℕ) : ℝ)^(t-2) * (n : ℝ)^(2-t) := by
    calc
      _ = ((p : ℕ) : ℝ)^(t-2) *
          (((p : ℕ) : ℝ)^(2-t) * (Nat.gcd n L : ℝ)^(2-t)) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hpR.le _)
  have hpw : (n : ℝ)^(2-t) = (n : ℝ)^2 * (n : ℝ)^(-t) := by
    rw [← Real.rpow_two, ← Real.rpow_add hnR]
    congr 1
  by_cases hnL : n ∣ L
  · simp only [sampleTerm, if_pos hnL]
    positivity
  · simp only [sampleTerm, if_neg hnL]
    calc
      _ ≤ (((p : ℕ) : ℝ)^(t-2) * (n : ℝ)^(2-t)) / (n : ℝ)^2 :=
        div_le_div_of_nonneg_right hg (sq_nonneg _)
      _ = _ := by rw [hpw]; field_simp

def sampleCoverTerm (t : ℝ) (L : ℕ) (p : Nat.Primes) (n : ℕ) : ℝ :=
  if (p : ℕ) ^ (L.factorization p + 1) ∣ n then
    ((p : ℕ) : ℝ)^(t-2) * (n : ℝ)^(-t) else 0

theorem sampleCoverTerm_nonneg (t : ℝ) (L : ℕ) (p : Nat.Primes) (n : ℕ) :
    0 ≤ sampleCoverTerm t L p n := by
  unfold sampleCoverTerm
  split_ifs <;> positivity

theorem sampleCoverTerm_summable (t : ℝ) (ht : 1 < t)
    (L : ℕ) (p : Nat.Primes) : Summable (sampleCoverTerm t L p) := by
  apply Summable.of_nonneg_of_le (sampleCoverTerm_nonneg t L p)
    (fun n => show sampleCoverTerm t L p n ≤
      ((p : ℕ) : ℝ)^(t-2) * (n : ℝ)^(-t) from by
        unfold sampleCoverTerm
        split_ifs
        · exact le_rfl
        · positivity)
  exact (Real.summable_nat_rpow.mpr (by linarith : -t < -1)).mul_left _

theorem sampleCoverTerm_tsum (t : ℝ) (L : ℕ) (p : Nat.Primes) :
    (∑' n : ℕ, sampleCoverTerm t L p n) =
      (∑' n : ℕ, (n : ℝ)^(-t)) * samplePrimeWeight t L p := by
  let q := (p : ℕ) ^ (L.factorization p + 1)
  have hq : 0 < q := pow_pos p.property.pos _
  have hi : Function.Injective (fun k : ℕ => q*k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hq hab
  have hr : Function.support (sampleCoverTerm t L p) ⊆
      Set.range (fun k : ℕ => q*k) := by
    intro n hn
    by_cases hd : q ∣ n
    · obtain ⟨k, hk⟩ := hd
      exact ⟨k, hk.symm⟩
    · have hz : sampleCoverTerm t L p n = 0 := by
        simp only [sampleCoverTerm, show ¬ (p : ℕ) ^ (L.factorization p+1) ∣ n from hd,
          if_false]
      exact False.elim (hn hz)
  calc
    _ = ∑' k : ℕ, sampleCoverTerm t L p (q*k) := (hi.tsum_eq hr).symm
    _ = ∑' k : ℕ, (((p : ℕ) : ℝ)^(t-2) * (q : ℝ)^(-t)) * (k : ℝ)^(-t) := by
      apply tsum_congr
      intro k
      simp only [sampleCoverTerm, show (p : ℕ) ^ (L.factorization p+1) ∣ q*k from
        dvd_mul_right q k, if_true, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg k)]
      ring
    _ = _ := by
      rw [tsum_mul_left]
      simp only [q, nat_pow_rpow, samplePrimeWeight, primeEscape]
      ring

theorem sampleTail_eq_tsum_unshifted (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (L : ℕ) : sampleTail t L = ∑' n : ℕ, sampleTerm t L n := by
  have hs : Summable (sampleTerm t L) := by
    apply Summable.of_nonneg_of_le (sampleTerm_nonneg t L) _
      ((summable_term t ht L).mul_left ((2 : ℝ)^(t-2)))
    intro n
    by_cases hn : n = 0
    · subst n
      simp [sampleTerm, term_zero t ht L]
    · exact sampleTerm_le_scaled_escape t ht2 L n (Nat.pos_of_ne_zero hn)
  have h := hs.tsum_eq_zero_add
  have hz : sampleTerm t L 0 = 0 := by simp [sampleTerm]
  rw [hz, zero_add] at h
  exact h.symm

theorem sampleTail_le_series_mul_samplePrimeWeight (t : ℝ) (ht : 1 < t)
    (ht2 : t ≤ 2) (L : ℕ) (hL : 0 < L) :
    sampleTail t L ≤ (∑' n : ℕ, (n : ℝ)^(-t)) *
      ∑' p : Nat.Primes, samplePrimeWeight t L p := by
  have houter : Summable (fun p : Nat.Primes =>
      ∑' n : ℕ, sampleCoverTerm t L p n) := by
    simpa only [sampleCoverTerm_tsum] using
      (samplePrimeWeight_summable t ht L).mul_left (∑' n : ℕ, (n : ℝ)^(-t))
  have hpair : Summable (Function.uncurry (sampleCoverTerm t L)) :=
    (summable_prod_of_nonneg (fun pn => sampleCoverTerm_nonneg t L pn.1 pn.2)).mpr
      ⟨sampleCoverTerm_summable t ht L, houter⟩
  have hmajor (n : ℕ) : sampleTerm t L n ≤ ∑' p : Nat.Primes,
      sampleCoverTerm t L p n := by
    by_cases hn : n = 0
    · subst n
      simpa [sampleTerm] using
        tsum_nonneg (fun p => sampleCoverTerm_nonneg t L p 0)
    by_cases hnL : n ∣ L
    · rw [sampleTerm, if_pos hnL]
      exact tsum_nonneg (fun p => sampleCoverTerm_nonneg t L p n)
    obtain ⟨p, hp⟩ := exists_prime_escape_of_not_dvd L n hL (Nat.pos_of_ne_zero hn) hnL
    have hp' : sampleCoverTerm t L p n ≤ ∑' q : Nat.Primes, sampleCoverTerm t L q n := by
      simpa only [Finset.sum_singleton, Function.uncurry, Prod.swap] using
        sum_le_hasSum ({p} : Finset Nat.Primes)
          (fun q _ => sampleCoverTerm_nonneg t L q n)
          (hpair.prod_symm.prod_factor n).hasSum
    exact (sampleTerm_le_prime_cover t ht2 L n hL (Nat.pos_of_ne_zero hn) p hp).trans
      (by simpa only [sampleCoverTerm, if_pos hp] using hp')
  have hs : Summable (sampleTerm t L) :=
    Summable.of_nonneg_of_le (sampleTerm_nonneg t L) hmajor hpair.prod_symm.prod
  rw [sampleTail_eq_tsum_unshifted t ht ht2 L]
  calc
    _ ≤ ∑' n : ℕ, ∑' p : Nat.Primes, sampleCoverTerm t L p n :=
      Summable.tsum_le_tsum hmajor hs hpair.prod_symm.prod
    _ = ∑' p : Nat.Primes, ∑' n : ℕ, sampleCoverTerm t L p n := hpair.tsum_comm
    _ = _ := by simp_rw [sampleCoverTerm_tsum]; rw [tsum_mul_left]


theorem samplePrimeWeight_lcmUpto_le_cutoff (t : ℝ) (ht : 1 < t)
    (M : ℕ) (hM : 0 < M) (p : Nat.Primes) :
    samplePrimeWeight t (Nat.lcmUpto M) p ≤
      (M : ℝ) ^ (-t) * ((p : ℕ) : ℝ) ^ (t - 2) := by
  calc
    _ ≤ ((p : ℕ) : ℝ) ^ (t - 2) * (M : ℝ) ^ (-t) :=
      mul_le_mul_of_nonneg_left (primeEscape_lcmUpto_le_cutoff t ht M hM p)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := mul_comm _ _

theorem samplePrimeWeight_lcmUpto_eq_prime_sq (t : ℝ) (M : ℕ)
    (p : Nat.Primes) (hMp : M < (p : ℕ)) :
    samplePrimeWeight t (Nat.lcmUpto M) p =
      ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  rw [samplePrimeWeight, primeEscape_lcmUpto_eq_power t M p hMp,
    ← Real.rpow_add hpR]
  congr 1; ring

/-- Exact separation of finite depth contributions and the complete large-prime tail. -/
theorem samplePrimeWeight_lcmUpto_split (t : ℝ) (M : ℕ) :
    (∑' p : Nat.Primes, samplePrimeWeight t (Nat.lcmUpto M) p) =
      (∑ p ∈ primePrefix M, samplePrimeWeight t (Nat.lcmUpto M) p) +
        primeTail 2 M := by
  classical
  let f : Nat.Primes → ℝ := fun p =>
    if p ∈ primePrefix M then samplePrimeWeight t (Nat.lcmUpto M) p else 0
  have hs : Summable f := by
    apply summable_of_ne_finset_zero (s := primePrefix M)
    intro p hp
    simp only [f, if_neg hp]
  have hsum : (∑' p : Nat.Primes, f p) =
      ∑ p ∈ primePrefix M, samplePrimeWeight t (Nat.lcmUpto M) p := by
    rw [tsum_eq_sum (s := primePrefix M) (by intro p hp; simp only [f, if_neg hp])]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [f, if_pos hp]
  calc
    _ = ∑' p : Nat.Primes, (f p +
        if M < (p : ℕ) then ((p : ℕ) : ℝ) ^ (-2 : ℝ) else 0) := by
      apply tsum_congr
      intro p
      by_cases hp : (p : ℕ) ≤ M
      · simp only [f, mem_primePrefix, if_pos hp, if_neg (not_lt.mpr hp), add_zero]
      · have hMp := Nat.lt_of_not_ge hp
        simp only [f, mem_primePrefix, if_neg hp, if_pos hMp, zero_add,
          samplePrimeWeight_lcmUpto_eq_prime_sq t M p hMp]
    _ = _ := by rw [hs.tsum_add (summable_primeTail 2 (by norm_num) M), hsum]; rfl

/-- The small-prime depth contribution has an explicit reciprocal-cutoff bound. -/
theorem samplePrimeWeight_small_le (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (M : ℕ) (hM : 0 < M) :
    (∑ p ∈ primePrefix M, samplePrimeWeight t (Nat.lcmUpto M) p) ≤
      1 / ((t - 1) * (M : ℝ)) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ ≤ ∑ p ∈ primePrefix M,
        (M : ℝ) ^ (-t) * ((p : ℕ) : ℝ) ^ (t - 2) :=
      Finset.sum_le_sum (fun p _ => samplePrimeWeight_lcmUpto_le_cutoff t ht M hM p)
    _ = (M : ℝ) ^ (-t) * ∑ p ∈ primePrefix M, ((p : ℕ) : ℝ) ^ (t - 2) := by
      rw [Finset.mul_sum]
    _ ≤ (M : ℝ) ^ (-t) * ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (t - 2) :=
      mul_le_mul_of_nonneg_left (primePrefix_rpow_le_Icc M (t - 2))
        (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    _ ≤ (M : ℝ) ^ (-t) * ((M : ℝ) ^ (t - 1) / (t - 1)) :=
      mul_le_mul_of_nonneg_left
        (RiemannResearch.NumberTheory.sum_Icc_rpow_sub_two_le M hM t ht ht2)
        (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    _ = _ := by
      rw [← mul_div_assoc, ← Real.rpow_add hMR,
        show -t + (t - 1) = (-1 : ℝ) by ring, Real.rpow_neg_one]
      field_simp [ne_of_gt hMR, ne_of_gt (show 0 < t - 1 by linarith)]

/-- The entire prime-power-weighted sampler budget has order at most 1/M. -/
theorem samplePrimeWeight_lcmUpto_sum_le (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (M : ℕ) (hM : 0 < M) :
    (∑' p : Nat.Primes, samplePrimeWeight t (Nat.lcmUpto M) p) ≤
      t / ((t - 1) * (M : ℝ)) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : primeTail 2 M ≤ 1 / (M : ℝ) := by
    have h := primeTail_le_rpow 2 (by norm_num) M hM
    norm_num only [show (1 : ℝ) - 2 = -1 by norm_num,
      show (2 : ℝ) - 1 = 1 by norm_num, div_one, Real.rpow_neg_one] at h
    simpa only [one_div] using h
  rw [samplePrimeWeight_lcmUpto_split t M]
  calc
    _ ≤ 1 / ((t - 1) * (M : ℝ)) + 1 / (M : ℝ) :=
      add_le_add (samplePrimeWeight_small_le t ht ht2 M hM) hp
    _ = _ := by
      field_simp [ne_of_gt hMR, ne_of_gt (show 0 < t - 1 by linarith)]
      ring

/-- The sharper complete gcd-sampler rate from the continuation note, with
both the small-prime-depth contribution and the infinite large-prime tail. -/
theorem sampleTail_lcmUpto_le_reciprocal (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (M : ℕ) (hM : 0 < M) :
    sampleTail t (Nat.lcmUpto M) ≤
      t * (∑' n : ℕ, (n : ℝ) ^ (-t)) / ((t - 1) * (M : ℝ)) := by
  calc
    _ ≤ (∑' n : ℕ, (n : ℝ) ^ (-t)) *
        ∑' p : Nat.Primes, samplePrimeWeight t (Nat.lcmUpto M) p :=
      sampleTail_le_series_mul_samplePrimeWeight t ht ht2 _ (Nat.lcmUpto_pos M)
    _ ≤ (∑' n : ℕ, (n : ℝ) ^ (-t)) * (t / ((t - 1) * (M : ℝ))) :=
      mul_le_mul_of_nonneg_left (samplePrimeWeight_lcmUpto_sum_le t ht ht2 M hM)
        (power_series_pos t ht).le
    _ = _ := by ring


/-- Explicit relative bound: the sampled tail is smaller than the raw escape
tail by a factor tending to zero throughout 1 < t < 2. -/
theorem sampleTail_div_tail_le (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (M : ℕ) (hM : 32 ≤ M) :
    sampleTail t (Nat.lcmUpto M) / tail t (Nat.lcmUpto M) ≤
      (t * (∑' n : ℕ, (n : ℝ)^(-t)) /
        ((t-1) * (4 * (32 : ℝ)^(-t)))) *
      (Real.log M / (M : ℝ)^(2-t)) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hb : 0 < 4 * (32 : ℝ)^(-t) := by positivity
  have htp : 0 < t-1 := by linarith
  have hD : 0 < tail t (Nat.lcmUpto M) :=
    tail_pos t ht ht2 _ (Nat.lcmUpto_pos M)
  let C := t * (∑' n : ℕ, (n : ℝ)^(-t)) / ((t-1) * (4 * (32 : ℝ)^(-t)))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (by linarith) (power_series_pos t ht).le)
      (mul_pos htp hb).le
  have hscale : 0 ≤ C * (Real.log M / (M : ℝ)^(2-t)) := by positivity
  apply (div_le_iff₀ hD).mpr
  calc
    _ ≤ t * (∑' n : ℕ, (n : ℝ)^(-t)) / ((t-1) * (M : ℝ)) :=
      sampleTail_lcmUpto_le_reciprocal t ht ht2 M (by omega)
    _ = (C * (Real.log M / (M : ℝ)^(2-t))) *
        (4 * (32 : ℝ)^(-t) * (M : ℝ)^(1-t) / Real.log M) := by
      dsimp [C]
      rw [show 2-t = 1+(1-t) by ring, Real.rpow_add hMR, Real.rpow_one]
      field_simp [ne_of_gt hMR, ne_of_gt hlog, ne_of_gt htp,
        ne_of_gt (Real.rpow_pos_of_pos (by norm_num : 0 < (32 : ℝ)) (-t)),
        ne_of_gt (Real.rpow_pos_of_pos hMR (1-t))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (tail_lcmUpto_lower_explicit t ht M hM) hscale

theorem sampleTail_div_tail_tendsto_zero (t : ℝ) (ht : 1 < t) (ht2 : t < 2) :
    Tendsto (fun M : ℕ => sampleTail t (Nat.lcmUpto M) /
      tail t (Nat.lcmUpto M)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun M : ℕ => Real.log M / (M : ℝ)^(2-t))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by linarith : 0 < 2-t)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop)
  have hb := hpow.const_mul
    (t * (∑' n : ℕ, (n : ℝ)^(-t)) / ((t-1) * (4 * (32 : ℝ)^(-t))))
  simp only [mul_zero] at hb
  apply squeeze_zero' (Eventually.of_forall (fun M =>
    div_nonneg (sampleTail_nonneg t _) (tail_nonneg t _))) ?_ hb
  filter_upwards [eventually_ge_atTop (32 : ℕ)] with M hM
  exact sampleTail_div_tail_le t ht ht2.le M hM

theorem eventually_sampleTail_le_mul_tail (t : ℝ) (ht : 1 < t) (ht2 : t < 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      sampleTail t (Nat.lcmUpto M) ≤ ε * tail t (Nat.lcmUpto M) := by
  have h := (sampleTail_div_tail_tendsto_zero t ht ht2).eventually
    (gt_mem_nhds hε)
  filter_upwards [h] with M hM
  exact ((div_lt_iff₀ (tail_pos t ht ht2.le _ (Nat.lcmUpto_pos M))).mp hM).le

/-- For a prime already present in the cutoff, the weighted escape starts
at its second power and gains the additional p^(-2) factor. -/
theorem samplePrimeWeight_lcmUpto_le_deep_power (t : ℝ) (ht : 1 < t)
    (M : ℕ) (p : Nat.Primes) (hpM : (p : ℕ) ≤ M) :
    samplePrimeWeight t (Nat.lcmUpto M) p ≤
      ((p : ℕ) : ℝ) ^ (-(t + 2)) := by
  have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  calc
    _ ≤ ((p : ℕ) : ℝ) ^ (t - 2) * ((p : ℕ) : ℝ) ^ (-(2 * t)) :=
      mul_le_mul_of_nonneg_left (primeEscape_lcmUpto_le_square t ht M p hpM)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by rw [← Real.rpow_add hpR]; congr 1; ring

/-- Retain a second prime threshold K, the small-prime depth sum, and the
entire medium-prime tail separately. No relation between K and M is needed. -/
theorem samplePrimeWeight_small_le_split (t : ℝ) (ht : 1 < t)
    (M K : ℕ) (hM : 0 < M) :
    (∑ p ∈ primePrefix M, samplePrimeWeight t (Nat.lcmUpto M) p) ≤
      (M : ℝ) ^ (-t) * (∑ p ∈ primePrefix K, ((p : ℕ) : ℝ) ^ (t - 2)) +
        primeTail (t + 2) K := by
  classical
  let a : Nat.Primes → ℝ := fun p =>
    if (p : ℕ) ≤ K then (M : ℝ) ^ (-t) * ((p : ℕ) : ℝ) ^ (t - 2) else 0
  let b : Nat.Primes → ℝ := fun p =>
    if K < (p : ℕ) then ((p : ℕ) : ℝ) ^ (-(t + 2)) else 0
  have ha0 (p : Nat.Primes) : 0 ≤ a p := by dsimp only [a]; split_ifs <;> positivity
  have hb0 (p : Nat.Primes) : 0 ≤ b p := by dsimp only [b]; split_ifs <;> positivity
  have ha : Summable a := by
    apply summable_of_ne_finset_zero (s := primePrefix K)
    intro p hp
    have hp' : ¬ (p : ℕ) ≤ K := by simpa only [mem_primePrefix] using hp
    simp only [a, if_neg hp']
  have hat : (∑' p : Nat.Primes, a p) =
      (M : ℝ) ^ (-t) * ∑ p ∈ primePrefix K, ((p : ℕ) : ℝ) ^ (t - 2) := by
    rw [tsum_eq_sum (s := primePrefix K) (by
      intro p hp
      have hp' : ¬ (p : ℕ) ≤ K := by simpa only [mem_primePrefix] using hp
      simp only [a, if_neg hp'])]
    calc
      _ = ∑ p ∈ primePrefix K, (M : ℝ) ^ (-t) * ((p : ℕ) : ℝ) ^ (t - 2) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [a, if_pos ((mem_primePrefix K p).mp hp)]
      _ = _ := by rw [Finset.mul_sum]
  have hb : Summable b := summable_primeTail (t + 2) (by linarith) K
  calc
    _ ≤ ∑ p ∈ primePrefix M, (a p + b p) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpK : (p : ℕ) ≤ K
      · simp only [a, b, if_pos hpK, if_neg (not_lt.mpr hpK), add_zero]
        exact samplePrimeWeight_lcmUpto_le_cutoff t ht M hM p
      · simp only [a, b, if_neg hpK, if_pos (Nat.lt_of_not_ge hpK), zero_add]
        exact samplePrimeWeight_lcmUpto_le_deep_power t ht M p
          ((mem_primePrefix M p).mp hp)
    _ ≤ ∑' p : Nat.Primes, (a p + b p) :=
      sum_le_hasSum (primePrefix M) (fun p _ => add_nonneg (ha0 p) (hb0 p))
        (ha.add hb).hasSum
    _ = _ := by rw [ha.tsum_add hb, hat]; rfl

/-- Explicit depth bound for arbitrary cutoff M and auxiliary threshold K. -/
theorem samplePrimeWeight_small_le_split_rpow (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (M K : ℕ) (hM : 0 < M) (hK : 0 < K) :
    (∑ p ∈ primePrefix M, samplePrimeWeight t (Nat.lcmUpto M) p) ≤
      (M : ℝ) ^ (-t) * (K : ℝ) ^ (t - 1) / (t - 1) +
        (K : ℝ) ^ (-t - 1) / (t + 1) := by
  have hprefix : (∑ p ∈ primePrefix K, ((p : ℕ) : ℝ) ^ (t - 2)) ≤
      (K : ℝ) ^ (t - 1) / (t - 1) :=
    (primePrefix_rpow_le_Icc K (t - 2)).trans
      (RiemannResearch.NumberTheory.sum_Icc_rpow_sub_two_le K hK t ht ht2)
  have htail : primeTail (t + 2) K ≤ (K : ℝ) ^ (-t - 1) / (t + 1) := by
    simpa only [show 1 - (t + 2) = -t - 1 by ring,
      show t + 2 - 1 = t + 1 by ring] using
      primeTail_le_rpow (t + 2) (by linarith) K hK
  calc
    _ ≤ (M : ℝ) ^ (-t) * (∑ p ∈ primePrefix K, ((p : ℕ) : ℝ) ^ (t - 2)) +
        primeTail (t + 2) K := samplePrimeWeight_small_le_split t ht M K hM
    _ ≤ (M : ℝ) ^ (-t) * ((K : ℝ) ^ (t - 1) / (t - 1)) +
        (K : ℝ) ^ (-t - 1) / (t + 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hprefix
        (Real.rpow_nonneg (Nat.cast_nonneg M) _)) htail
    _ = _ := by ring

/-- On square cutoffs the prime-depth budget is smaller than order 1/M.
The unsquared large-prime tail remains visible and is the dominant term. -/
theorem samplePrimeWeight_lcmUpto_square_sum_le (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (K : ℕ) (hK : 0 < K) :
    (∑' p : Nat.Primes, samplePrimeWeight t (Nat.lcmUpto (K ^ 2)) p) ≤
      (1 / (t - 1) + 1 / (t + 1)) * (K : ℝ) ^ (-t - 1) +
        primeTail 2 (K ^ 2) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have he : ((K ^ 2 : ℕ) : ℝ) ^ (-t) * (K : ℝ) ^ (t - 1) =
      (K : ℝ) ^ (-t - 1) := by
    rw [Nat.cast_pow, pow_two, Real.mul_rpow hKR.le hKR.le,
      ← Real.rpow_add hKR, ← Real.rpow_add hKR]
    congr 1; ring
  rw [samplePrimeWeight_lcmUpto_split t (K ^ 2)]
  apply add_le_add _ le_rfl
  calc
    _ ≤ ((K ^ 2 : ℕ) : ℝ) ^ (-t) * (K : ℝ) ^ (t - 1) / (t - 1) +
        (K : ℝ) ^ (-t - 1) / (t + 1) :=
      samplePrimeWeight_small_le_split_rpow t ht ht2 (K ^ 2) K (by positivity) hK
    _ = _ := by rw [he]; ring

/-- Sharper complete sampler bound retaining the actual prime tail. Its
Chebyshev bound yields order 1/(M log M), with M=K^2. -/
theorem sampleTail_lcmUpto_square_le (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2)
    (K : ℕ) (hK : 0 < K) :
    sampleTail t (Nat.lcmUpto (K ^ 2)) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-t)) *
        ((1 / (t - 1) + 1 / (t + 1)) * (K : ℝ) ^ (-t - 1) +
          primeTail 2 (K ^ 2)) :=
  (sampleTail_le_series_mul_samplePrimeWeight t ht ht2 _ (Nat.lcmUpto_pos _)).trans
    (mul_le_mul_of_nonneg_left (samplePrimeWeight_lcmUpto_square_sum_le t ht ht2 K hK)
      (power_series_pos t ht).le)

/-- The nonnegative-power side of the integer square-root comparison. -/
private theorem nat_sqrt_rpow_le_half (M : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (Nat.sqrt M : ℝ) ^ a ≤ (M : ℝ) ^ (a / 2) := by
  have hs : (Nat.sqrt M : ℝ) ^ 2 ≤ (M : ℝ) := by
    exact_mod_cast Nat.sqrt_le' M
  calc
    _ = ((Nat.sqrt M : ℝ) ^ 2) ^ (a / 2) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg (Nat.sqrt M)) 2 (a / 2)]
      congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) hs (by linarith)

/-- For positive M, its integer square root is at least sqrt(M)/2.
This form avoids division by a square root and applies directly to real powers. -/
private theorem nat_sqrt_neg_rpow_le (M : ℕ) (hM : 0 < M)
    (a : ℝ) (ha : 0 ≤ a) :
    (Nat.sqrt M : ℝ) ^ (-a) ≤
      (2 : ℝ) ^ a * (M : ℝ) ^ (-a / 2) := by
  have hK : 0 < Nat.sqrt M := Nat.sqrt_pos.mpr hM
  have hKR : (0 : ℝ) < Nat.sqrt M := by exact_mod_cast hK
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hfourN : M ≤ 4 * (Nat.sqrt M) ^ 2 := by
    have htwo : Nat.sqrt M + 1 ≤ 2 * Nat.sqrt M := by omega
    have hm := Nat.mul_le_mul htwo htwo
    have hs := Nat.lt_succ_sqrt M
    nlinarith
  have hfour : (M : ℝ) ≤ 4 * (Nat.sqrt M : ℝ) ^ 2 := by
    exact_mod_cast hfourN
  have hp : (4 * (Nat.sqrt M : ℝ) ^ 2) ^ (-a / 2) ≤
      (M : ℝ) ^ (-a / 2) :=
    Real.rpow_le_rpow_of_nonpos hMR hfour (by linarith)
  have h4 : (4 : ℝ) ^ (-a / 2) = (2 : ℝ) ^ (-a) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) 2 (-a / 2)]
    congr 1; ring
  have hsq : ((Nat.sqrt M : ℝ) ^ 2) ^ (-a / 2) =
      (Nat.sqrt M : ℝ) ^ (-a) := by
    rw [← Real.rpow_natCast_mul hKR.le 2 (-a / 2)]
    congr 1; ring
  calc
    _ = (2 : ℝ) ^ a * (4 * (Nat.sqrt M : ℝ) ^ 2) ^ (-a / 2) := by
      rw [Real.mul_rpow (by norm_num : 0 ≤ (4 : ℝ)) (sq_nonneg _),
        h4, hsq, ← mul_assoc, ← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num) _)

/-- At every positive cutoff, choosing the auxiliary threshold floor(sqrt M)
gives a smaller depth term of order M^(-(t+1)/2). The entire large-prime tail
remains explicit. No monotonicity of the actual sampled tail is assumed. -/
theorem samplePrimeWeight_lcmUpto_sum_le_sqrt_split
    (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) (M : ℕ) (hM : 0 < M) :
    (∑' p : Nat.Primes, samplePrimeWeight t (Nat.lcmUpto M) p) ≤
      (1 / (t - 1) + (2 : ℝ) ^ (t + 1) / (t + 1)) *
        (M : ℝ) ^ (-(t + 1) / 2) + primeTail 2 M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hK : 0 < Nat.sqrt M := Nat.sqrt_pos.mpr hM
  have hfirst : (M : ℝ) ^ (-t) * (Nat.sqrt M : ℝ) ^ (t - 1) /
      (t - 1) ≤ (M : ℝ) ^ (-(t + 1) / 2) / (t - 1) := by
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ t - 1)
    calc
      _ ≤ (M : ℝ) ^ (-t) * (M : ℝ) ^ ((t - 1) / 2) :=
        mul_le_mul_of_nonneg_left
          (nat_sqrt_rpow_le_half M (t - 1) (by linarith))
          (Real.rpow_nonneg hMR.le _)
      _ = _ := by rw [← Real.rpow_add hMR]; congr 1; ring
  have hsecond : (Nat.sqrt M : ℝ) ^ (-t - 1) / (t + 1) ≤
      ((2 : ℝ) ^ (t + 1) * (M : ℝ) ^ (-(t + 1) / 2)) / (t + 1) := by
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ t + 1)
    simpa only [show -t - 1 = -(t + 1) by ring] using
      nat_sqrt_neg_rpow_le M hM (t + 1) (by linarith)
  rw [samplePrimeWeight_lcmUpto_split t M]
  apply add_le_add _ le_rfl
  calc
    _ ≤ (M : ℝ) ^ (-t) * (Nat.sqrt M : ℝ) ^ (t - 1) / (t - 1) +
        (Nat.sqrt M : ℝ) ^ (-t - 1) / (t + 1) :=
      samplePrimeWeight_small_le_split_rpow t ht ht2 M (Nat.sqrt M) hM hK
    _ ≤ (M : ℝ) ^ (-(t + 1) / 2) / (t - 1) +
        ((2 : ℝ) ^ (t + 1) * (M : ℝ) ^ (-(t + 1) / 2)) / (t + 1) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

/-- The complete gcd-sampler estimate at every positive LCM cutoff. -/
theorem sampleTail_lcmUpto_le_sqrt_split
    (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) (M : ℕ) (hM : 0 < M) :
    sampleTail t (Nat.lcmUpto M) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-t)) *
        ((1 / (t - 1) + (2 : ℝ) ^ (t + 1) / (t + 1)) *
          (M : ℝ) ^ (-(t + 1) / 2) + primeTail 2 M) :=
  (sampleTail_le_series_mul_samplePrimeWeight t ht ht2 _ (Nat.lcmUpto_pos _)).trans
    (mul_le_mul_of_nonneg_left
      (samplePrimeWeight_lcmUpto_sum_le_sqrt_split t ht ht2 M hM)
      (power_series_pos t ht).le)

/-- Every cutoff retains a faster depth term plus an explicit 1/(M log M)
large-prime term. For fixed t>1 the depth term is asymptotically smaller. -/
theorem sampleTail_lcmUpto_le_explicit_log
    (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) (M : ℕ) (hM : 1 < M) :
    sampleTail t (Nat.lcmUpto M) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-t)) *
        ((1 / (t - 1) + (2 : ℝ) ^ (t + 1) / (t + 1)) *
          (M : ℝ) ^ (-(t + 1) / 2) +
          4 * (2 * Real.log 4 + 2) / ((M : ℝ) * Real.log M)) := by
  apply (sampleTail_lcmUpto_le_sqrt_split t ht ht2 M (by omega)).trans
  apply mul_le_mul_of_nonneg_left _ (power_series_pos t ht).le
  exact add_le_add le_rfl (primeTail_two_le_explicit_log M hM)

/-- An explicit eventual bound of order 1/(M log M), at every LCM cutoff. -/
theorem eventually_sampleTail_lcmUpto_le_log
    (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) :
    ∀ᶠ M : ℕ in atTop, sampleTail t (Nat.lcmUpto M) ≤
      (∑' n : ℕ, (n : ℝ)^(-t)) *
        (1/(t-1) + (2 : ℝ)^(t+1)/(t+1) + 4*(2*Real.log 4+2)) /
          ((M : ℝ) * Real.log M) := by
  have hp : Tendsto (fun M : ℕ => Real.log M / (M : ℝ)^((t-1)/2))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by linarith : 0 < (t-1)/2)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop)
  have he := hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_ge_atTop (2 : ℕ)] with M hratio hM
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogpow : Real.log M ≤ (M : ℝ)^((t-1)/2) := by
    have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hMR ((t-1)/2))).mp hratio
    simpa only [one_mul] using h.le
  have hdepth : (M : ℝ)^(-(t+1)/2) ≤ 1/((M : ℝ)*Real.log M) := by
    apply (le_div_iff₀ (mul_pos hMR hlog)).mpr
    calc
      _ ≤ (M : ℝ)^(-(t+1)/2) * ((M : ℝ) * (M : ℝ)^((t-1)/2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogpow hMR.le)
          (Real.rpow_nonneg hMR.le _)
      _ = (M : ℝ)^(-(t+1)/2 + 1 + (t-1)/2) := by
        rw [Real.rpow_add hMR, Real.rpow_add hMR, Real.rpow_one]
        ring
      _ = 1 := by rw [show -(t+1)/2 + 1 + (t-1)/2 = 0 by ring, Real.rpow_zero]
  have hC : 0 ≤ 1/(t-1) + (2 : ℝ)^(t+1)/(t+1) := by
    have h1 : 0 < t-1 := by linarith
    have h2 : 0 < t+1 := by linarith
    positivity
  calc
    _ ≤ (∑' n : ℕ, (n : ℝ)^(-t)) *
        ((1/(t-1) + (2 : ℝ)^(t+1)/(t+1)) * (M : ℝ)^(-(t+1)/2) +
          4*(2*Real.log 4+2)/((M : ℝ)*Real.log M)) :=
      sampleTail_lcmUpto_le_explicit_log t ht ht2 M (by omega)
    _ ≤ (∑' n : ℕ, (n : ℝ)^(-t)) *
        ((1/(t-1) + (2 : ℝ)^(t+1)/(t+1)) * (1/((M : ℝ)*Real.log M)) +
          4*(2*Real.log 4+2)/((M : ℝ)*Real.log M)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hdepth hC) le_rfl)
        (power_series_pos t ht).le
    _ = _ := by ring

end RiemannResearch.NumberTheory.DivisorEscapeTail
