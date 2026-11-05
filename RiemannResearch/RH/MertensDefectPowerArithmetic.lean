/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.CanonicalMobiusWindowCancellation
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Defs
import RiemannResearch.RH.ArithmeticFloorHyperbolaPowerBounds
import Mathlib.Tactic.FieldSimp

/-!
# Signed floor sums and power bounds for the canonical Möbius defect

Source: the user-provided Mertens displacement archive.
-/
noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.PrimeNumberTheorem

private theorem mobius_Icc_eq_M_nat (t : ℕ) :
    (∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)) = M (t : ℝ) := by
  unfold M
  rw [Nat.floor_natCast]
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_Iic.mpr (Finset.mem_Icc.mp hi).2
  · intro i hi hnot
    have ht := Finset.mem_Iic.mp hi
    have hi0 : i = 0 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      omega
    subst i; simp

/-- Exact signed defect at every positive physical site. The sum is empty
on the head. No Mertens estimate or squarefreeness is required. -/
theorem canonicalMobiusHead_defect_eq_mertens_sum (N n : ℕ) (hn : 0 < n) :
    1 - canonicalMobiusHead N n = (∑ k ∈ Finset.Icc 1 (n/(N+1)),
      (M ((n/k : ℕ):ℝ) - M (N:ℝ))) +
      ((N+1 : ℕ):ℝ) * mobiusReciprocalSum N * ((n/(N+1) : ℕ):ℝ) := by
  by_cases hNn : N ≤ n
  · have h := finite_mobius_floor_tail_identity N n hn hNn
    simp_rw [mobius_Icc_eq_M_nat] at h
    rw [canonicalMobiusHead_floor_expansion]
    linarith only [h]
  · have hq : n/(N+1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [hq, canonicalMobiusHead_exact N n hn (by omega)]

/-- Collect the constant part of each Mertens block into the signed correction. -/
theorem canonicalMobiusHead_defect_eq_grouped_mertens_sum (N n : ℕ) (hn : 0 < n) :
    1 - canonicalMobiusHead N n = (∑ k ∈ Finset.Icc 1 (n/(N+1)), M ((n/k : ℕ):ℝ)) +
      ((n/(N+1) : ℕ):ℝ) * (((N+1 : ℕ):ℝ) * mobiusReciprocalSum N - M (N:ℝ)) := by
  rw [canonicalMobiusHead_defect_eq_mertens_sum N n hn, Finset.sum_sub_distrib]
  simp [Nat.card_Icc, nsmul_eq_mul]
  <;> ring

/-- The pointwise defect of the canonical Möbius head under an ordinary
power bound with exponent `s ∈ (0,1)` and a reciprocal bound at this head.
The ordinary estimate is needed only at cutoffs at least `N`. -/
theorem canonicalMobiusHead_defect_le_min_of_M_power
    (N n : ℕ) (hN : 0 < N) (hn : 0 < n)
    (s C D : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ t : ℕ, N ≤ t → |M (t : ℝ)| ≤ C * (t : ℝ) ^ s)
    (hm : |mobiusReciprocalSum N| ≤ D * (N : ℝ) ^ (s-1)) :
    |1 - canonicalMobiusHead N n| ≤ min (3 * (N : ℝ))
      ((2 * C / (1-s) + D) * ((n : ℝ) * (N : ℝ) ^ (s-1))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h1s : 0 < 1-s := by linarith
  apply le_min
  · calc
      _ ≤ |(1 : ℝ)| + |canonicalMobiusHead N n| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (1 : ℝ) (-canonicalMobiusHead N n)
      _ ≤ _ := by rw [abs_one]; linarith [canonicalMobiusHead_abs_le_two_mul N hN n]
  · by_cases hnN : n ≤ N
    · rw [canonicalMobiusHead_exact N n hn hnN, sub_self, abs_zero]
      positivity
    let q : ℕ := n/(N+1)
    let T : ℝ := ∑ k ∈ Finset.Icc 1 q, (M ((n/k : ℕ):ℝ) - M (N:ℝ))
    have hqprod : q*(N+1) ≤ n := Nat.div_mul_le_self n (N+1)
    have hqn : (q : ℝ) ≤ (n : ℝ)/(N : ℝ) := by
      apply (le_div_iff₀ hNr).2
      exact_mod_cast (Nat.mul_le_mul_left q (Nat.le_succ N)).trans hqprod
    have term (k : ℕ) (hk : k ∈ Finset.Icc 1 q) :
        |M ((n/k : ℕ):ℝ) - M (N:ℝ)| ≤ (2*C*(n:ℝ)^s)*(k:ℝ)^(-s) := by
      have hk' := Finset.mem_Icc.mp hk
      have hk0 : 0 < k := by omega
      have hkr : (0:ℝ) < k := by exact_mod_cast hk0
      have hkprod : k*(N+1) ≤ n := (Nat.le_div_iff_mul_le (Nat.succ_pos N)).mp hk'.2
      have hY : N+1 ≤ n/k := (Nat.le_div_iff_mul_le hk0).2 (by simpa [Nat.mul_comm] using hkprod)
      have hNk : N ≤ n/k := by omega
      have hquot : ((n/k : ℕ):ℝ) ≤ (n:ℝ)/(k:ℝ) :=
        (le_div_iff₀ hkr).2 (by exact_mod_cast Nat.div_mul_le_self n k)
      have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (n/k)) hquot hs
      have hpowN := Real.rpow_le_rpow hNr.le
        (show (N:ℝ) ≤ ((n/k : ℕ):ℝ) by exact_mod_cast hNk) hs
      have hlo := (hM _ hNk).trans (mul_le_mul_of_nonneg_left hpow hC)
      have hhi := (hM _ le_rfl).trans (mul_le_mul_of_nonneg_left (hpowN.trans hpow) hC)
      calc
        _ ≤ |M ((n/k:ℕ):ℝ)| + |M (N:ℝ)| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (M ((n/k:ℕ):ℝ)) (-M (N:ℝ))
        _ ≤ C*((n:ℝ)/(k:ℝ))^s + C*((n:ℝ)/(k:ℝ))^s := add_le_add hlo hhi
        _ = _ := by rw [Real.div_rpow hnr.le hkr.le, Real.rpow_neg hkr.le]; ring
    have hpower : (n:ℝ)^s * ((n:ℝ)/(N:ℝ))^(1-s) = (n:ℝ)*(N:ℝ)^(s-1) := by
      rw [Real.div_rpow hnr.le hNr.le, ← mul_div_assoc, ← Real.rpow_add hnr,
        show s + (1-s) = 1 by ring, Real.rpow_one,
        show s-1 = -(1-s) by ring, Real.rpow_neg hNr.le, div_eq_mul_inv]
    have htail : |T| ≤ (2*C/(1-s)) * ((n:ℝ)*(N:ℝ)^(s-1)) := by
      have hp : (∑ k ∈ Finset.Icc 1 q, (k : ℝ) ^ (-s)) ≤
          (q : ℝ) ^ (1-s) / (1-s) := by
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
        simpa only [Nat.add_sub_cancel, Nat.add_comm 1] using
          sum_nat_succ_neg_rpow_le hs hs1 q
      have hB : 0 ≤ 2*C*(n:ℝ)^s := by positivity
      calc
        |T| ≤ ∑ k ∈ Finset.Icc 1 q, |M ((n/k:ℕ):ℝ) - M (N:ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.Icc 1 q, (2*C*(n:ℝ)^s)*(k:ℝ)^(-s) := Finset.sum_le_sum term
        _ = (2*C*(n:ℝ)^s) * ∑ k ∈ Finset.Icc 1 q, (k:ℝ)^(-s) := by rw [Finset.mul_sum]
        _ ≤ (2*C*(n:ℝ)^s) * ((q:ℝ)^(1-s)/(1-s)) := mul_le_mul_of_nonneg_left hp hB
        _ ≤ (2*C*(n:ℝ)^s) * (((n:ℝ)/(N:ℝ))^(1-s)/(1-s)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (Real.rpow_le_rpow (Nat.cast_nonneg q) hqn h1s.le) h1s.le) hB
        _ = (2*C/(1-s))*((n:ℝ)^s * ((n:ℝ)/(N:ℝ))^(1-s)) := by ring
        _ = _ := by rw [hpower]
    have hcorr : |((N+1 : ℕ):ℝ) * mobiusReciprocalSum N * (q:ℝ)| ≤
        D * ((n:ℝ)*(N:ℝ)^(s-1)) := by
      simp only [abs_mul,
        abs_of_nonneg (show 0 ≤ ((N+1 : ℕ) : ℝ) from Nat.cast_nonneg _),
        abs_of_nonneg (show 0 ≤ (q : ℝ) from Nat.cast_nonneg q)]
      have hprod : (q:ℝ)*((N+1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hqprod
      calc
        _ ≤ ((N+1:ℕ):ℝ)*(D*(N:ℝ)^(s-1))*(q:ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
        _ = (D*(N:ℝ)^(s-1))*((q:ℝ)*((N+1:ℕ):ℝ)) := by ring
        _ ≤ (D*(N:ℝ)^(s-1))*(n:ℝ) := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = _ := by ring
    have hid : 1 - canonicalMobiusHead N n = T + ((N+1:ℕ):ℝ)*mobiusReciprocalSum N*(q:ℝ) :=
      canonicalMobiusHead_defect_eq_mertens_sum N n hn
    rw [hid]
    calc
      _ ≤ |T| + |((N+1:ℕ):ℝ)*mobiusReciprocalSum N*(q:ℝ)| := abs_add_le _ _
      _ ≤ (2*C/(1-s)) * ((n:ℝ)*(N:ℝ)^(s-1)) + D * ((n:ℝ)*(N:ℝ)^(s-1)) :=
        add_le_add htail hcorr
      _ = _ := by ring

end RiemannResearch.RH.Pareto
