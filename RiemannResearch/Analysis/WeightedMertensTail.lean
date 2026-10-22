/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.WeightedMertensTransfer
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Signed density tails from logarithmic summatory cancellation

Proof strategy: exact Abel summation (`Mathlib.NumberTheory.AbelSummation`),
followed by the integral of a power and the series limit. These generic
real-coefficient results feed the Burnol half-damping arithmetic endpoint.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis

private theorem rpowContinuous (r b : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ r) (Icc 1 b) := by
  apply ContinuousOn.rpow_const continuousOn_id
  intro x hx
  exact Or.inl (show x ≠ 0 by linarith [hx.1])

def threeHalfWeightedPrefix (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n * (n : ℝ) ^ (-3 / 2 : ℝ)

theorem threeHalfWeightedPrefix_abel (c : ℕ → ℝ) (hc : c 0 = 0) (x : ℝ) :
    threeHalfWeightedPrefix c x = x ^ (-3 / 2 : ℝ) * arithmeticSummatory c x +
      (3 / 2 : ℝ) * ∫ t in Ioc 1 x,
        t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t := by
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :
      HasDerivAt (fun y : ℝ => y ^ (-3 / 2 : ℝ))
        ((-3 / 2 : ℝ) * t ^ (-5 / 2 : ℝ)) t := by
    convert Real.hasDerivAt_rpow_const (x := t) (p := (-3 / 2 : ℝ))
      (Or.inl (ne_of_gt (by linarith [ht.1]))) using 1 <;> norm_num
  have hdc : ContinuousOn (deriv (fun y : ℝ => y ^ (-3 / 2 : ℝ)))
      (Icc 1 x) := by
    apply ((rpowContinuous (-5 / 2) x).const_mul (-3 / 2)).congr
    intro t ht
    exact (hd t ht).deriv
  have ha := sum_mul_eq_sub_integral_mul₀ c hc x
    (fun t ht => (hd t ht).differentiableAt) hdc.integrableOn_Icc
  have hi : (∫ t in Ioc 1 x,
      deriv (fun y : ℝ => y ^ (-3 / 2 : ℝ)) t * arithmeticSummatory c t) =
      (-3 / 2 : ℝ) * ∫ t in Ioc 1 x,
        t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
    ring
  change (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℝ) ^ (-3 / 2 : ℝ) * c n) =
    x ^ (-3 / 2 : ℝ) * arithmeticSummatory c x -
      ∫ t in Ioc 1 x,
        deriv (fun y : ℝ => y ^ (-3 / 2 : ℝ)) t * arithmeticSummatory c t at ha
  rw [hi] at ha
  unfold threeHalfWeightedPrefix
  simp_rw [mul_comm (c _) _]
  linarith

theorem shiftedLogProfile_antitone {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    shiftedLogProfile x ≤ shiftedLogProfile y := by
  unfold shiftedLogProfile
  apply Real.rpow_le_rpow_of_nonpos (shiftedLog_pos hy)
  · linarith [Real.log_le_log (by linarith : 0 < y) hyx]
  · norm_num

theorem threeHalfWeightedPrefix_difference_abel (c : ℕ → ℝ) (hc : c 0 = 0)
    {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    threeHalfWeightedPrefix c x - threeHalfWeightedPrefix c y =
      x ^ (-3 / 2 : ℝ) * arithmeticSummatory c x -
      y ^ (-3 / 2 : ℝ) * arithmeticSummatory c y +
      (3 / 2 : ℝ) * ∫ t in Ioc y x,
        t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t := by
  let g : ℝ → ℝ := fun t => t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t
  have hi : IntegrableOn g (Ioc 1 x) := by
    exact (integrableOn_mul_sum_Icc c (m := 0) (by norm_num : (0 : ℝ) ≤ 1)
      (rpowContinuous (-5 / 2) x).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hi1y : IntervalIntegrable g volume 1 y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy]
    exact hi.mono_set (fun t ht => ⟨ht.1, ht.2.trans hyx⟩)
  have hiyx : IntervalIntegrable g volume y x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hyx]
    exact hi.mono_set (fun t ht => ⟨lt_of_le_of_lt hy ht.1, ht.2⟩)
  have he := intervalIntegral.integral_add_adjacent_intervals hi1y hiyx
  rw [intervalIntegral.integral_of_le hy, intervalIntegral.integral_of_le hyx,
    intervalIntegral.integral_of_le (hy.trans hyx)] at he
  rw [threeHalfWeightedPrefix_abel c hc, threeHalfWeightedPrefix_abel c hc]
  dsimp [g] at he
  linarith

/-- A finite reciprocal-density tail estimate. The constant five permits the
right boundary to be controlled uniformly before taking any infinite limit. -/
theorem threeHalfWeightedPrefix_difference_bound (c : ℕ → ℝ) (hc : c 0 = 0)
    {B x y : ℝ} (hB : 0 ≤ B) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hM : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory c t| ≤ B * t * shiftedLogProfile t) :
    |threeHalfWeightedPrefix c x - threeHalfWeightedPrefix c y| ≤
      5 * B * y ^ (-1 / 2 : ℝ) * shiftedLogProfile y := by
  have hy0 : 0 < y := by linarith
  have hprof : 0 ≤ shiftedLogProfile y :=
    Real.rpow_nonneg (shiftedLog_pos hy).le _
  have hboundary (t : ℝ) (ht : y ≤ t) :
      |t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| ≤
        B * y ^ (-1 / 2 : ℝ) * shiftedLogProfile y := by
    have ht0 : 0 < t := hy0.trans_le ht
    have hp : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
      calc
        _ = t ^ (-3 / 2 : ℝ) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add ht0]; norm_num
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc
      _ ≤ t ^ (-3 / 2 : ℝ) * (B * t * shiftedLogProfile t) :=
        mul_le_mul_of_nonneg_left (hM t (hy.trans ht)) (Real.rpow_nonneg ht0.le _)
      _ = B * t ^ (-1 / 2 : ℝ) * shiftedLogProfile t := by
        calc
          _ = B * (t ^ (-3 / 2 : ℝ) * t) * shiftedLogProfile t := by ring
          _ = _ := by rw [hp]
      _ ≤ _ := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hy0 ht (by norm_num)) hB
        · exact shiftedLogProfile_antitone hy ht
        · exact Real.rpow_nonneg (shiftedLog_pos (hy.trans ht)).le _
        · positivity
  have hi : IntegrableOn
      (fun t => t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t) (Ioc y x) := by
    apply (integrableOn_mul_sum_Icc c (m := 0) (by norm_num : (0 : ℝ) ≤ 1)
      (rpowContinuous (-5 / 2) x).integrableOn_Icc).mono_set
    intro t ht
    exact ⟨hy.trans ht.1.le, ht.2⟩
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Ioi y) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hy0
  have hpowint : (∫ t in Ioi y, t ^ (-3 / 2 : ℝ)) = 2 * y ^ (-1 / 2 : ℝ) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hy0]
    norm_num
    ring
  have hIntBound : |∫ t in Ioc y x,
      t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t| ≤
        2 * B * y ^ (-1 / 2 : ℝ) * shiftedLogProfile y := by
    calc
      _ ≤ ∫ t in Ioc y x, |t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioc y x, (B * shiftedLogProfile y) * t ^ (-3 / 2 : ℝ) := by
        apply integral_mono_ae hi.abs
          ((hpow.mono_set (fun t ht => ht.1)).const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 < t := hy0.trans ht.1
        have hp : t ^ (-5 / 2 : ℝ) * t = t ^ (-3 / 2 : ℝ) := by
          calc
            _ = t ^ (-5 / 2 : ℝ) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add ht0]; norm_num
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        calc
          _ ≤ t ^ (-5 / 2 : ℝ) * (B * t * shiftedLogProfile t) :=
            mul_le_mul_of_nonneg_left (hM t (hy.trans ht.1.le))
              (Real.rpow_nonneg ht0.le _)
          _ = B * t ^ (-3 / 2 : ℝ) * shiftedLogProfile t := by
            calc
              _ = B * (t ^ (-5 / 2 : ℝ) * t) * shiftedLogProfile t := by ring
              _ = _ := by rw [hp]
          _ ≤ _ := by
            have := mul_le_mul_of_nonneg_left (shiftedLogProfile_antitone hy ht.1.le)
              (mul_nonneg hB (Real.rpow_nonneg ht0.le (-3 / 2)))
            nlinarith
      _ ≤ ∫ t in Ioi y, (B * shiftedLogProfile y) * t ^ (-3 / 2 : ℝ) := by
        apply setIntegral_mono_set (hpow.const_mul _)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (mul_nonneg hB hprof)
            (Real.rpow_nonneg (le_of_lt (hy0.trans ht)) _)
        · exact Filter.Eventually.of_forall (fun t ht => ht.1)
      _ = _ := by rw [integral_const_mul, hpowint]; ring
  rw [threeHalfWeightedPrefix_difference_abel c hc hy hyx]
  have htri := abs_add_le
    (x ^ (-3 / 2 : ℝ) * arithmeticSummatory c x -
      y ^ (-3 / 2 : ℝ) * arithmeticSummatory c y)
    ((3 / 2 : ℝ) * ∫ t in Ioc y x,
      t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t)
  have hsub := abs_sub_le
    (x ^ (-3 / 2 : ℝ) * arithmeticSummatory c x) 0
    (y ^ (-3 / 2 : ℝ) * arithmeticSummatory c y)
  simp only [sub_zero, zero_sub, abs_neg] at hsub
  rw [abs_mul (3 / 2 : ℝ)] at htri
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at htri
  nlinarith [hboundary x hyx, hboundary y le_rfl]

theorem threeHalfWeightedPrefix_tendsto (c : ℕ → ℝ)
    (hs : Summable (fun n : ℕ => c n * (n : ℝ) ^ (-3 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => threeHalfWeightedPrefix c N) atTop
      (𝓝 (∑' n : ℕ, c n * (n : ℝ) ^ (-3 / 2 : ℝ))) := by
  have he (N : ℕ) : threeHalfWeightedPrefix c N =
      ∑ n ∈ Finset.range (N + 1), c n * (n : ℝ) ^ (-3 / 2 : ℝ) := by
    unfold threeHalfWeightedPrefix
    rw [Nat.floor_natCast]
    congr 1
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  simp_rw [he]
  exact hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- The infinite density tail inherits the same logarithmic saving as the
summatory function. Absolute summability of the density series is explicit. -/
theorem threeHalfWeightedPrefix_tail_bound (c : ℕ → ℝ) (hc : c 0 = 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory c t| ≤ B * t * shiftedLogProfile t)
    (hs : Summable (fun n : ℕ => c n * (n : ℝ) ^ (-3 / 2 : ℝ)))
    {y : ℕ} (hy : 1 ≤ y) :
    |(∑' n : ℕ, c n * (n : ℝ) ^ (-3 / 2 : ℝ)) - threeHalfWeightedPrefix c y| ≤
      5 * B * (y : ℝ) ^ (-1 / 2 : ℝ) * shiftedLogProfile y := by
  apply le_of_tendsto ((threeHalfWeightedPrefix_tendsto c hs).sub_const
    (threeHalfWeightedPrefix c y)).abs
  filter_upwards [eventually_ge_atTop y] with N hN
  exact threeHalfWeightedPrefix_difference_bound c hc hB
    (by exact_mod_cast hy) (by exact_mod_cast hN) hM

end RiemannResearch.Analysis
