/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensAllLogPowers
import RiemannResearch.Analysis.WeightedMertensLogPowerTail
import RiemannResearch.RH.DampedMobiusJointHeadLimits

/-!
# Unconditional all-logarithmic signed half-damped providers

Each natural logarithmic exponent has its own finite constant. The Mertens
provider discharges every arithmetic premise. The shift 6+4k preserves
monotonicity globally and changes only the exponent-dependent constant.
No uniform control in k, stretched-exponential rate, or fixed subhalf
finite-energy statement is asserted.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
open RiemannResearch.Analysis

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem M_logPowerShift_bound (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * shiftedLogPowerProfile k x := by
  obtain ⟨B, hB, hM⟩ := M_shiftedLog_all_nat_powers k
  let A : ℝ := ((k : ℝ) + 1) ^ k
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro x hx
  have hL := shiftedLog_pos hx
  have hS := shiftedLogPower_pos k hx
  have hshift : logPowerShift k + Real.log x ≤
      ((k : ℝ) + 1) * (6 + Real.log x) := by
    dsimp [logPowerShift]
    have hk := Nat.cast_nonneg (α := ℝ) k
    have hl := Real.log_nonneg hx
    nlinarith
  have hpow := pow_le_pow_left₀ hS.le hshift k
  rw [mul_pow] at hpow
  have hweighted : |M x| * (logPowerShift k + Real.log x) ^ k ≤ A * B * x := by
    have h1 := mul_le_mul_of_nonneg_left hpow (abs_nonneg (M x))
    have h2 := mul_le_mul_of_nonneg_left (hM x hx) hA
    dsimp [A] at h2 ⊢
    nlinarith only [h1, h2]
  have hprofile : 0 ≤ shiftedLogPowerProfile k x :=
    Real.rpow_nonneg hS.le _
  have hcancel : (logPowerShift k + Real.log x) ^ k *
      shiftedLogPowerProfile k x = 1 := by
    unfold shiftedLogPowerProfile
    rw [← Real.rpow_natCast, ← Real.rpow_add hS]
    simp
  have h := mul_le_mul_of_nonneg_right hweighted hprofile
  simpa only [mul_assoc, hcancel, mul_one] using h

end RiemannResearch.NumberTheory.PrimeNumberTheorem

namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.PrimeNumberTheorem

private theorem arithmeticSummatory_moebius (x : ℝ) :
    arithmeticSummatory (fun n => (ArithmeticFunction.moebius n : ℝ)) x = M x := by
  unfold arithmeticSummatory M
  apply Finset.sum_congr
  · ext n
    simp
  · intro n hn
    rfl

private theorem halfWeightedPrefix_moebius (N : ℕ) :
    halfWeightedPrefix (fun n => (ArithmeticFunction.moebius n : ℝ)) (N : ℝ) =
      positiveArithmeticPrefix (dampedMobiusWeight (1 / 2)) N := by
  unfold halfWeightedPrefix
  rw [Nat.floor_natCast]
  have hi : Finset.Icc 0 N = Finset.range (N + 1) := by ext n; simp
  rw [hi, Finset.sum_range_succ']
  norm_num [positiveArithmeticPrefix, dampedMobiusWeight]

theorem dampedMobius_half_prefix_all_log_bound (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℕ, 0 < t →
      |positiveArithmeticPrefix (dampedMobiusWeight (1 / 2)) t| ≤
        B * Real.sqrt (t : ℝ) /
          (logPowerShift k + Real.log (t : ℝ)) ^ (k : ℝ) := by
  obtain ⟨B, hB, hM⟩ := M_logPowerShift_bound k
  have hMu : ∀ x : ℝ, 1 ≤ x →
      |arithmeticSummatory (fun n => (ArithmeticFunction.moebius n : ℝ)) x| ≤
        B * x * shiftedLogPowerProfile k x := by
    simpa only [arithmeticSummatory_moebius] using hM
  refine ⟨3 * B, by positivity, ?_⟩
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have h := halfWeightedPrefix_log_power_bound k
    (fun n => (ArithmeticFunction.moebius n : ℝ)) (by simp) hB ht1 hMu
  rw [halfWeightedPrefix_moebius, halfLogPowerPrimitive_eq_sqrt_div k ht1] at h
  simpa only [mul_div_assoc] using h

/-- PNT supplies a signed density-tail saving at the half-damping endpoint. -/
theorem dampedMobius_half_density_tail_all_log_bound (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ M : ℕ, 1 ≤ M →
      |(1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re -
        positiveArithmeticPrefix (fun d => dampedMobiusWeight (1 / 2) d / (d : ℝ)) M| ≤
        D * (M : ℝ) ^ (-1 / 2 : ℝ) *
          (logPowerShift k + Real.log (M : ℝ)) ^ (-(k : ℝ)) := by
  let c := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ)
  have hc : c 0 = 0 := by simp [c]
  have hterm (n : ℕ) : c n * (n : ℝ) ^ (-3 / 2 : ℝ) =
      dampedMobiusWeight (1 / 2) n / (n : ℝ) := by
    rw [dampedMobiusWeight_div]
    norm_num only [show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num]
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    simp only [c, div_eq_mul_inv]
  have hs : HasSum (fun n => c n * (n : ℝ) ^ (-3 / 2 : ℝ))
      (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re := by
    simp_rw [hterm]
    have h := (hasSum_nat_add_iff
      (f := fun n => dampedMobiusWeight (1 / 2) n / (n : ℝ)) 1).mp
      (dampedMobius_density_hasSum (by norm_num : (0 : ℝ) < 1 / 2))
    simpa only [Finset.sum_range_one, dampedMobiusWeight_zero, Nat.cast_zero,
      zero_div, add_zero] using h
  have hp (M : ℕ) : threeHalfWeightedPrefix c (M : ℝ) =
      ∑ m ∈ Finset.range M, dampedMobiusWeight (1 / 2) (m + 1) / ((m + 1 : ℕ) : ℝ) := by
    unfold threeHalfWeightedPrefix
    rw [Nat.floor_natCast]
    have hi : Finset.Icc 0 M = Finset.range (M + 1) := by ext n; simp
    rw [hi, Finset.sum_range_succ']
    simp only [hc, zero_mul, add_zero, hterm]
  obtain ⟨B, hB, hM⟩ := M_logPowerShift_bound k
  have hMu : ∀ x : ℝ, 1 ≤ x → |arithmeticSummatory c x| ≤
      B * x * shiftedLogPowerProfile k x := by
    have hid (x : ℝ) : arithmeticSummatory c x = M x := by
      unfold arithmeticSummatory M
      apply Finset.sum_congr
      · ext n
        simp
      · intro n hn
        rfl
    simpa only [hid] using hM
  refine ⟨5 * B, by positivity, ?_⟩
  intro M hM
  have h := threeHalfWeightedPrefix_log_power_tail_bound k c hc hB hMu hs.summable hM
  simpa only [hs.tsum_eq, hp, shiftedLogPowerProfile, positiveArithmeticPrefix] using h

end RiemannResearch.RH.Pareto
