/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeMobiusSubtree
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Counting the moving prime subtree at a cubic cutoff
Source: Section 9 of *Prime trees, fractional parts, and zeta zeros*.
The count below is exact at each prime; applying the prime number theorem
to it gives the asymptotic in that section. -/

noncomputable section
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder

private theorem coefficient_of_le_prime_square {p k : ℕ} (hk : 1 < k) (hbound : k ≤ p ^ 2) :
    coefficient (Nat.primesLE p) k = if p < k ∧ k.Prime then -1 else 0 := by
  classical
  by_cases hgood : ∀ q ∈ Nat.primesLE p, ¬q ∣ k
  · have hmin : p < k.minFac := by
      by_contra! hm
      exact hgood k.minFac (Nat.mem_primesLE.mpr ⟨hm, Nat.minFac_prime (by omega)⟩)
        (Nat.minFac_dvd k)
    have hprime : k.Prime := by
      by_contra h
      have hs := Nat.minFac_sq_le_self (show 0 < k by omega) h
      have hgt := Nat.mul_self_lt_mul_self hmin
      nlinarith only [hs, hbound, hgt]
    have hpk : p < k := by simpa only [hprime.minFac_eq] using hmin
    simp only [coefficient, if_pos hgood, if_pos (And.intro hpk hprime),
      ArithmeticFunction.moebius_apply_prime hprime, Int.cast_neg, Int.cast_one]
  · have hb : ¬(p < k ∧ k.Prime) := by
      rintro ⟨hpk, hkprime⟩
      apply hgood
      intro q hq hdiv
      have he := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primesLE hq) hkprime).mp hdiv
      have hle := Nat.le_of_mem_primesLE hq
      omega
    simp [coefficient, hgood, hb]

private theorem root_le_square (p : ℕ) (hp : p.Prime) : p ≤ p^2 := by
  simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left p hp.one_le

private theorem count_succ (n : ℕ) :
    (Nat.primeCounting (n+1) : ℝ) =
      (Nat.primeCounting n : ℝ) + (if (n+1).Prime then 1 else 0) := by
  classical
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_succ]
  by_cases h : (n+1).Prime <;> simp [h, Nat.notMem_primesLE]

private theorem roughSum_start (p : ℕ) (hp : p.Prime) : roughSum (Nat.primesLE p) p = 1 := by
  have ht : ∀ n : ℕ, 0 < n → n ≤ p → roughSum (Nat.primesLE p) n = 1 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn1 hnp
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hgood : ∀ q ∈ Nat.primesLE p, ¬q ∣ (1 : ℕ) :=
          fun q hq => (Nat.prime_of_mem_primesLE hq).not_dvd_one
        have hc : coefficient (Nat.primesLE p) 1 = 1 := by
          rw [coefficient, if_pos hgood]
          norm_num
        simp [roughSum, hc]
      · have hrec : roughSum (Nat.primesLE p) (n+1) = roughSum (Nat.primesLE p) n
              + coefficient (Nat.primesLE p) (n+1) := Finset.sum_range_succ _ _
        rw [hrec, ih hn (by omega), coefficient_of_le_prime_square (by omega)
          (hnp.trans (root_le_square p hp)), if_neg (fun h => (Nat.not_lt.mpr hnp) h.1)]
        simp
  exact ht p hp.pos le_rfl

/-- At `p³` only the root `p` and the children `p*q` for `p<q≤p²`
can contribute. In particular the signed squarefree count is a prime-count
difference at every prime, including `p=2`. -/
theorem cylinder_at_prime_cube {p : ℕ} (hp : p.Prime) :
    cylinder p (Nat.primesLE p) (p^3) =
      (Nat.primeCounting (p^2) : ℝ) - (Nat.primeCounting p : ℝ) - 1 := by
  have hinterval (n : ℕ) (hn : p ≤ n) (hbound : n ≤ p^2) :
      roughSum (Nat.primesLE p) n =
        1 + (Nat.primeCounting p : ℝ) - (Nat.primeCounting n : ℝ) := by
    induction n, hn using Nat.le_induction with
    | base => rw [roughSum_start p hp]; ring
    | succ n hn ih =>
      have hrec : roughSum (Nat.primesLE p) (n+1) = roughSum (Nat.primesLE p) n
          + coefficient (Nat.primesLE p) (n+1) := Finset.sum_range_succ _ _
      have hgt : p < n+1 := by omega
      have htwo : 1 < n+1 := hp.one_lt.trans hgt
      rw [hrec, ih (by omega), coefficient_of_le_prime_square htwo hbound, count_succ]
      by_cases h : (n+1).Prime
      · simp [hgt,h]
        ring
      · simp [hgt,h]
  have hcover : ∀ q, q.Prime → q ∣ p → q ∈ Nat.primesLE p :=
    fun q hq hd => Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hp.pos hd, hq⟩
  have hdiv : p^3 / p = p^2 := by
    rw [show p^3 = p*p^2 by ring, Nat.mul_div_cancel_left _ hp.pos]
  rw [cylinder_eq_roughSum (Nat.primesLE p) hcover, hdiv,
    ArithmeticFunction.moebius_apply_prime hp, hinterval _ (root_le_square p hp) le_rfl]
  push_cast
  ring

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
