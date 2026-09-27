/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensStretchedDecay
import RiemannResearch.Analysis.WeightedMertensLoglogStretched
import RiemannResearch.RH.DampedMobiusJointHeadLimits

/-!
# Unconditional weighted providers for the optimized profile

See `RH/MertensStretchedContinuation20260927.md` for the provider audit,
finite optimization, and scope of the result.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
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

/-- One common positive exponential coefficient controls both signed arithmetic
providers. All arithmetic premises are supplied by the full-PNT bootstrap. -/
theorem dampedMobius_half_loglog_stretched_providers :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 8 ∧ ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧
      (∀ t : ℕ, 0 < t →
        |positiveArithmeticPrefix (dampedMobiusWeight (1 / 2)) t| ≤
          B * Real.sqrt (t : ℝ) * loglogStretchedProfile (1 / 11) d t) ∧
      (∀ t : ℕ, 0 < t →
        |(1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re -
          positiveArithmeticPrefix
            (fun m => dampedMobiusWeight (1 / 2) m / (m : ℝ)) t| ≤
          D * (t : ℝ) ^ (-1 / 2 : ℝ) * loglogStretchedProfile (1 / 11) d t) := by
  obtain ⟨c, hc, C, hC, hM⟩ := M_stretched_loglog_bound
  let d : ℝ := min c (1 / 8)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd8 : d ≤ 1 / 8 := min_le_right _ _
  have hdc : d ≤ c := min_le_left _ _
  let K : ℝ := C
  have hK : 0 ≤ K := hC
  have hMb : ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ K * x * loglogStretchedProfile (1 / 11) d x := by
    intro x hx
    have hprofile : loglogStretchedProfile (1 / 11) c x ≤
        loglogStretchedProfile (1 / 11) d x := by
      unfold loglogStretchedProfile
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hdc
        (Real.rpow_nonneg (stretchedLoglogCore_pos hx).le (1 / 11 : ℝ))
      nlinarith
    have hm := hM x hx
    change |M x| ≤ C * x * loglogStretchedProfile (1 / 11) c x at hm
    calc
      _ ≤ C * x * loglogStretchedProfile (1 / 11) c x := hm
      _ ≤ C * x * loglogStretchedProfile (1 / 11) d x :=
        mul_le_mul_of_nonneg_left hprofile (mul_nonneg hC (by linarith))
      _ = _ := rfl
  have hMu : ∀ x : ℝ, 1 ≤ x →
      |arithmeticSummatory (fun n => (ArithmeticFunction.moebius n : ℝ)) x| ≤
        K * x * loglogStretchedProfile (1 / 11) d x := by
    simpa only [arithmeticSummatory_moebius] using hMb
  let a := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ)
  have hc : a 0 = 0 := by simp [a]
  have hterm (n : ℕ) : a n * (n : ℝ) ^ (-3 / 2 : ℝ) =
      dampedMobiusWeight (1 / 2) n / (n : ℝ) := by
    rw [dampedMobiusWeight_div]
    norm_num only [show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num]
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    simp only [a, div_eq_mul_inv]
  have hs : HasSum (fun n => a n * (n : ℝ) ^ (-3 / 2 : ℝ))
      (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re := by
    simp_rw [hterm]
    have h := (hasSum_nat_add_iff
      (f := fun n => dampedMobiusWeight (1 / 2) n / (n : ℝ)) 1).mp
      (dampedMobius_density_hasSum (by norm_num : (0 : ℝ) < 1 / 2))
    simpa only [Finset.sum_range_one, dampedMobiusWeight_zero, Nat.cast_zero,
      zero_div, add_zero] using h
  have hp (M : ℕ) : threeHalfWeightedPrefix a (M : ℝ) =
      ∑ m ∈ Finset.range M, dampedMobiusWeight (1 / 2) (m + 1) / ((m + 1 : ℕ) : ℝ) := by
    unfold threeHalfWeightedPrefix
    rw [Nat.floor_natCast]
    have hi : Finset.Icc 0 M = Finset.range (M + 1) := by ext n; simp
    rw [hi, Finset.sum_range_succ']
    simp only [hc, zero_mul, add_zero, hterm]

  refine ⟨d, hd, hd8, 3 * K, 5 * K, by positivity, by positivity, ?_, ?_⟩
  · intro t ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have h := halfWeightedPrefix_loglog_stretched_bound (1 / 11) d
      (by norm_num) (by norm_num) hd.le hd8
      (fun n => (ArithmeticFunction.moebius n : ℝ)) (by simp) hK ht1 hMu
    rw [halfWeightedPrefix_moebius, halfLoglogStretchedPrimitive_eq_sqrt] at h
    simpa only [mul_assoc] using h
  · intro t ht
    have h := threeHalfWeightedPrefix_loglog_stretched_tail_bound (1 / 11) d
      (by norm_num) hd.le a hc hK hMu hs.summable ht
    simpa only [hs.tsum_eq, hp, positiveArithmeticPrefix] using h

end RiemannResearch.RH.Pareto
