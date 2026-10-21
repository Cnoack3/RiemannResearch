/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerSignedSieve
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoCoordinateDual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Physical prime jumps control signed sieve coefficients

Source: the user-requested three-stage signed-sieve investigation, 21 October
2026. These are actual coordinate and complete-Q norm inequalities. They do
not replace the full signed Gram identity by a diagonal approximation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative SquarefreeRadicalDifference

theorem qDifference_sieveVector (L p n : ℕ) (hL : 0 < L) (hn : 1 ≤ n) :
    qDifference (sieveVector L p) n =
      (if Nat.gcd n L = p then 1 else 0) - sieveSlope L p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [qDifference, Nat.succ_eq_add_one, Nat.add_sub_cancel, qSequence_sieveVector _ _ _ hL,
    sieveCount, cumulative_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem gcd_semiprime_primorial_eq_iff (p q K : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpK : p ≤ K) (hpq : p < q) :
    Nat.gcd (p * q) (primorial K) = p ↔ K < q := by
  constructor
  · intro he
    by_contra h
    have hqK : q ≤ K := by omega
    have hqd : q ∣ Nat.gcd (p * q) (primorial K) :=
      Nat.dvd_gcd (dvd_mul_left q p) (hq.dvd_primorial_iff.mpr hqK)
    rw [he] at hqd
    have heq := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqd
    omega
  · intro hKq
    have hcop : Nat.Coprime q (primorial K) := hq.coprime_iff_not_dvd.mpr
      (by rw [hq.dvd_primorial_iff]; omega)
    have he : Nat.gcd (p * q) (primorial K) = Nat.gcd p (primorial K) := by
      simpa only [Nat.mul_comm] using hcop.gcd_mul_left_cancel p
    rw [he, Nat.gcd_eq_left_iff_dvd]
    exact hp.dvd_primorial_iff.mpr hpK

theorem qDifference_sieveVector_semiprime (p q K : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpK : p ≤ K) (hpq : p < q) :
    qDifference (sieveVector (primorial K) p) (p * q) =
      (if K < q then 1 else 0) - sieveSlope (primorial K) p := by
  rw [qDifference_sieveVector _ _ _ (primorial_pos K)
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hq.ne_zero))]
  simp only [gcd_semiprime_primorial_eq_iff p q K hp hq hpK hpq]

/-- The mass constraint is unnecessary: zero drift exposes the cumulative
coefficient at each semiprime site exactly. -/
theorem signedSieveVector_semiprime_jump (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (S : Finset ℕ) (w : ℕ → ℝ)
    (hcut : ∀ K ∈ S, p ≤ K)
    (hd : ∑ K ∈ S, w K * sieveSlope (primorial K) p = 0) :
    qDifference (signedSieveVector p S w) (p * q) =
      ∑ K ∈ S, if K < q then w K else 0 := by
  have hs (n : ℕ) : qSequence (signedSieveVector p S w) n =
      ∑ K ∈ S, w K * qSequence (sieveVector (primorial K) p) n := by
    change qSequenceLinear (∑ K ∈ S, w K • _) n = _
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [qDifference, hs, hs, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ K ∈ S, w K * ((if K < q then 1 else 0) - sieveSlope (primorial K) p) := by
      apply Finset.sum_congr rfl
      intro K hK
      rw [← mul_sub, ← qDifference,
        qDifference_sieveVector_semiprime p q K hp hq (hcut K hK) hpq]
    _ = _ := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hd, sub_zero]
      apply Finset.sum_congr rfl
      intro K hK
      split_ifs <;> ring

theorem qSequence_abs_le (f : QHilbert) (n : ℕ) :
    |qSequence f n| ≤ Real.sqrt zetaTwo * (n : ℝ) * ‖f‖ := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hr := qSiteRiesz_norm_sq n hnpos
  have he : ‖qSiteRiesz n‖ = Real.sqrt zetaTwo * (n : ℝ) := by
    have h0 := norm_nonneg (qSiteRiesz n)
    have h1 : 0 ≤ Real.sqrt zetaTwo * (n : ℝ) := by positivity
    have hz := Real.sq_sqrt zetaTwo_pos.le
    nlinarith
  rw [← qSiteRiesz_inner n hnpos f]
  simpa only [he] using abs_real_inner_le_norm (qSiteRiesz n) f

/-- A coarse but uniform complete-Q bound for a physical jump. -/
theorem qDifference_abs_le (f : QHilbert) (n : ℕ) :
    |qDifference f n| ≤ 2 * Real.sqrt zetaTwo * (n : ℝ) * ‖f‖ := by
  have h1 := qSequence_abs_le f n
  have h2 := qSequence_abs_le f (n - 1)
  have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg zetaTwo)) (norm_nonneg f)
  have ht := abs_sub_le (qSequence f n) 0 (qSequence f (n - 1))
  simp only [sub_zero, zero_sub, abs_neg] at ht
  change |qSequence f n - qSequence f (n - 1)| ≤ _
  nlinarith

theorem signedSieveVector_prefix_energy_bound (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (S : Finset ℕ) (w : ℕ → ℝ)
    (hcut : ∀ K ∈ S, p ≤ K)
    (hd : ∑ K ∈ S, w K * sieveSlope (primorial K) p = 0) :
    |∑ K ∈ S, if K < q then w K else 0| ≤
      2 * Real.sqrt zetaTwo * (p * q : ℕ) * ‖signedSieveVector p S w‖ := by
  rw [← signedSieveVector_semiprime_jump p q hp hq hpq S w hcut hd]
  exact qDifference_abs_le _ _

end RiemannResearch.RH.QPrimePowerSieve
