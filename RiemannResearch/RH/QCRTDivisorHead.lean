/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.ParetoReflectionVariance

/-!
# Exact CRT divisor heads and their full-period mean

Source: user-provided CRT/Parseval construction request, 13 October 2026.

The density repair is legal and makes every covered positive head exact.
Its full-period reflection constant is the conductor times the sieve density.
The resulting exact mean and finite energy floor retain the tail obstruction.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTDivisorHead
open ArithmeticCumulative QPrimeSieve Pareto ZetaTwoProbability

def candidate (L n : ℕ) : ℝ :=
  divisorSieve L n + (L : ℝ) * divisorDensity L * residueFraction L n

theorem candidate_eq_count (L n : ℕ) (hL : 0 < L) :
    candidate L n = coprimeCount L n -
      (L : ℝ) * divisorDensity L * ((n / L : ℕ) : ℝ) := by
  rw [candidate, divisorSieve_eq_count_sub_linear L n (ne_of_gt hL),
    residueFraction_eq_div_sub_floor L n hL]
  have hLR : (L : ℝ) ≠ 0 := by positivity
  field_simp [hLR]
  ring

theorem candidate_exact_head (L M n : ℕ) (hL : 0 < L)
    (hML : M < L) (hn : 0 < n) (hnM : n ≤ M)
    (hcover : ∀ k, 2 ≤ k → k ≤ M → ¬ Nat.Coprime k L) :
    candidate L n = 1 := by
  rw [candidate_eq_count L n hL, coprimeCount_head L M n hn hnM hcover,
    Nat.div_eq_of_lt (lt_of_le_of_lt hnM hML)]
  simp

theorem candidate_period (L n : ℕ) : candidate L (n + L) = candidate L n := by
  unfold candidate divisorSieve residueFraction
  have hs : (∑ d ∈ L.divisors,
      (ArithmeticFunction.moebius d : ℝ) * ((n + L) % d : ℕ) / (d : ℝ)) =
      ∑ d ∈ L.divisors,
      (ArithmeticFunction.moebius d : ℝ) * (n % d : ℕ) / (d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd)]
    simp
  simp_rw [← mul_div_assoc]
  rw [hs]
  simp

private theorem residueFraction_reflect (L d n : ℕ) (hd : 0 < d)
    (hdL : d ∣ L) (hn : n < L) :
    residueFraction d n + residueFraction d (L - 1 - n) =
      1 - 1 / (d : ℝ) := by
  have h := residue_reflection_sum hd hdL hn
  rw [Nat.cast_sub (Nat.succ_le_of_lt hd), Nat.cast_one] at h
  change Pareto.residue d n / (d : ℝ) +
    Pareto.residue d (L - 1 - n) / (d : ℝ) = _
  rw [← add_div, h]
  have hdR : (d : ℝ) ≠ 0 := by positivity
  field_simp [hdR]

private theorem moebius_divisor_sum_zero (L : ℕ) (hL : 1 < L) :
    (∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
  have h := divisor_sift L 0 (by omega)
  simpa [divisorIndicator, Nat.coprime_zero_left, ne_of_gt hL] using h

theorem candidate_reflection (L n : ℕ) (hL : 1 < L) (hn : n < L) :
    candidate L n + candidate L (L - 1 - n) = (L : ℝ) * divisorDensity L := by
  have hs : (∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
      (residueFraction d n + residueFraction d (L - 1 - n))) =
      -divisorDensity L := by
    calc
      _ = ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
          (1 - 1 / (d : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [residueFraction_reflect L d n (Nat.pos_of_mem_divisors hd)
          (Nat.dvd_of_mem_divisors hd) hn]
      _ = _ := by
        simp only [mul_sub, mul_one, mul_one_div, Finset.sum_sub_distrib,
          moebius_divisor_sum_zero L hL, zero_sub, divisorDensity]
  have hpair := residueFraction_reflect L L n (by omega) (dvd_refl L) hn
  have hLR : (L : ℝ) ≠ 0 := by positivity
  unfold candidate divisorSieve
  simp_rw [mul_add, Finset.sum_add_distrib] at hs
  calc
    _ = -((∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
          residueFraction d n) +
        ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
          residueFraction d (L - 1 - n)) +
        (L : ℝ) * divisorDensity L *
          (residueFraction L n + residueFraction L (L - 1 - n)) := by ring
    _ = -(-divisorDensity L) + (L : ℝ) * divisorDensity L *
        (1 - 1 / (L : ℝ)) := by rw [hs, hpair]
    _ = _ := by field_simp [hLR]; ring

theorem candidate_uniform_mean (L : ℕ) (hL : 1 < L) :
    (∑ r : Fin L, candidate L r.val) / L =
      (L : ℝ) * divisorDensity L / 2 :=
  reflection_uniform_mean L (by omega) (candidate L)
    ((L : ℝ) * divisorDensity L) (fun n hn => candidate_reflection L n hL hn)

/-- Complete finite error decomposition before discarding any variance. -/
theorem candidate_uniform_error_identity (L : ℕ) (hL : 1 < L) :
    (∑ r : Fin L, (1 - candidate L r.val) ^ 2) =
      (∑ r : Fin L,
        (candidate L r.val - (L : ℝ) * divisorDensity L / 2) ^ 2) +
      (L : ℝ) * (1 - (L : ℝ) * divisorDensity L / 2) ^ 2 := by
  have hmean := candidate_uniform_mean L hL
  have hLR : (L : ℝ) ≠ 0 := by positivity
  have hsum : (∑ r : Fin L, candidate L r.val) =
      (L : ℝ) * ((L : ℝ) * divisorDensity L / 2) := by
    apply (div_eq_iff hLR).mp at hmean
    nlinarith [hmean]
  simp only [sub_sq, one_pow, mul_one, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  ring

theorem candidate_uniform_error_lower (L : ℕ) (hL : 1 < L) :
    (L : ℝ) * (1 - (L : ℝ) * divisorDensity L / 2) ^ 2 ≤
      ∑ r : Fin L, (1 - candidate L r.val) ^ 2 := by
  rw [candidate_uniform_error_identity L hL]
  have hv : 0 ≤ ∑ r : Fin L,
      (candidate L r.val - (L : ℝ) * divisorDensity L / 2) ^ 2 :=
    Finset.sum_nonneg (fun r _ => sq_nonneg _)
  linarith

@[simp] theorem candidate_zero (L : ℕ) : candidate L 0 = 0 := by
  simp [candidate, divisorSieve, residueFraction]

@[simp] theorem candidate_conductor (L : ℕ) : candidate L L = 0 := by
  simpa using candidate_period L 0

theorem candidate_abs_le (L : ℕ) (hL : 0 < L) (n : ℕ) :
    |candidate L n| ≤ (L.divisors.card : ℝ) +
      |(L : ℝ) * divisorDensity L| := by
  unfold candidate
  calc
    _ ≤ |divisorSieve L n| +
        |(L : ℝ) * divisorDensity L * residueFraction L n| := abs_add_le _ _
    _ ≤ (L.divisors.card : ℝ) + |(L : ℝ) * divisorDensity L| := by
      apply add_le_add (divisorSieve_abs_le L n)
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left
        (Pareto.residueFraction_abs_le_one L n hL)
        (abs_nonneg ((L : ℝ) * divisorDensity L))

private theorem candidate_error_sum_shift (L : ℕ) :
    (∑ r : Fin L, (1 - candidate L r.val) ^ 2) =
      ∑ r : Fin L, (1 - candidate L (r.val + 1)) ^ 2 := by
  cases L with
  | zero => simp
  | succ k =>
    have hleft : (∑ r : Fin (k + 1), (1 - candidate (k + 1) r.val) ^ 2) =
        (1 - candidate (k + 1) 0) ^ 2 +
          ∑ r : Fin k, (1 - candidate (k + 1) (r.val + 1)) ^ 2 := by
      rw [Fin.sum_univ_succ]
      rfl
    have hright : (∑ r : Fin (k + 1),
        (1 - candidate (k + 1) (r.val + 1)) ^ 2) =
        (∑ r : Fin k, (1 - candidate (k + 1) (r.val + 1)) ^ 2) +
          (1 - candidate (k + 1) (k + 1)) ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hleft, hright, candidate_zero, candidate_conductor]
    ring

/-- The entire first period is bounded below by the exact reflection mean.
The head is exact, so this lower bound is necessarily carried by its tail. -/
theorem candidate_headError_lower (L : ℕ) (hL : 1 < L) :
    (1 - (L : ℝ) * divisorDensity L / 2) ^ 2 / (zetaTwo * (L : ℝ)) ≤
      headError L (candidate L) := by
  have hLR : (0 : ℝ) < L := by positivity
  have hZ : 0 < zetaTwo := zetaTwo_pos
  have hmin := div_le_div_of_nonneg_right (candidate_uniform_error_lower L hL)
    (show 0 ≤ zetaTwo * (L : ℝ) ^ 2 by positivity)
  have hsimp : (L : ℝ) * (1 - (L : ℝ) * divisorDensity L / 2) ^ 2 /
      (zetaTwo * (L : ℝ) ^ 2) =
      (1 - (L : ℝ) * divisorDensity L / 2) ^ 2 / (zetaTwo * (L : ℝ)) := by
    field_simp [ne_of_gt hLR, ne_of_gt hZ]
  rw [hsimp, candidate_error_sum_shift] at hmin
  have hcast : (∑ r : Fin L, (1 - candidate L (r.val + 1)) ^ 2) =
      ∑ k ∈ Finset.range L, (1 - candidate L (k + 1)) ^ 2 := by
    exact Fin.sum_univ_eq_sum_range (fun k : ℕ => (1 - candidate L (k + 1)) ^ 2) L
  rw [hcast] at hmin
  apply hmin.trans
  unfold headError
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  have hkL : ((k + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (show k + 1 ≤ L by have := Finset.mem_range.mp hk; omega)
  have hkR : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left (by nlinarith :
    ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (L : ℝ) ^ 2) hZ.le

/-- Unconditional lower bound for the full, literal squared L²(Q) error.
This is not merely a uniform-residue or truncated proxy. -/
theorem candidate_fullError_lower (L : ℕ) (hL : 1 < L) :
    (1 - (L : ℝ) * divisorDensity L / 2) ^ 2 / (zetaTwo * (L : ℝ)) ≤
      fullError (candidate L) := by
  apply (candidate_headError_lower L hL).trans
  apply headError_le_fullError
  exact fullError_summable_of_abs_le (candidate L)
    ((L.divisors.card : ℝ) + |(L : ℝ) * divisorDensity L|)
    (candidate_abs_le L (by omega))

end RiemannResearch.RH.QCRTDivisorHead
