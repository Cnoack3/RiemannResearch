/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.WeightedMertensTransfer
import RiemannResearch.Analysis.PositiveArithmeticPrefix
import RiemannResearch.Analysis.PowerLogProfiles
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Reciprocal density tails from one signed prefix estimate

The proof is exact Abel summation followed by a power integral. It removes
the independent density-tail hypothesis from the arithmetic hyperbola
criterion. The signed prefix estimate itself remains an explicit hypothesis.
Source: standard Abel summation, as in Mathlib.NumberTheory.AbelSummation;
the finite-bound implementation extends WeightedMertensTail.
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

/-- Real summatory functions and positive natural prefixes agree at the floor. -/
theorem arithmeticSummatory_eq_positiveArithmeticPrefix (w : ℕ → ℝ)
    (hw0 : w 0 = 0) (x : ℝ) :
    arithmeticSummatory w x = positiveArithmeticPrefix w ⌊x⌋₊ := by
  have hfin : Finset.Icc 0 ⌊x⌋₊ = Finset.range (⌊x⌋₊ + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  rw [arithmeticSummatory, hfin, Finset.sum_range_succ']
  simp only [hw0, add_zero, positiveArithmeticPrefix]

private theorem reciprocalSummatory_abel (w : ℕ → ℝ) (hw0 : w 0 = 0)
    (x : ℝ) :
    arithmeticSummatory (fun n => w n / (n : ℝ)) x =
      x ^ (-1 : ℝ) * arithmeticSummatory w x +
        ∫ t in Ioc 1 x, t ^ (-2 : ℝ) * arithmeticSummatory w t := by
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :
      HasDerivAt (fun y : ℝ => y ^ (-1 : ℝ))
        (-(t ^ (-2 : ℝ))) t := by
    convert Real.hasDerivAt_rpow_const (x := t) (p := (-1 : ℝ))
      (Or.inl (ne_of_gt (by linarith [ht.1]))) using 1
    norm_num
  have hdc : ContinuousOn (deriv (fun y : ℝ => y ^ (-1 : ℝ)))
      (Icc 1 x) := by
    apply (rpowContinuous (-2) x).neg.congr
    intro t ht
    exact (hd t ht).deriv
  have ha := sum_mul_eq_sub_integral_mul₀ w hw0 x
    (fun t ht => (hd t ht).differentiableAt) hdc.integrableOn_Icc
  have hi : (∫ t in Ioc 1 x,
      deriv (fun y : ℝ => y ^ (-1 : ℝ)) t * arithmeticSummatory w t) =
      -(∫ t in Ioc 1 x, t ^ (-2 : ℝ) * arithmeticSummatory w t) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
    ring
  change (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℝ) ^ (-1 : ℝ) * w n) =
    x ^ (-1 : ℝ) * arithmeticSummatory w x -
      ∫ t in Ioc 1 x,
        deriv (fun y : ℝ => y ^ (-1 : ℝ)) t * arithmeticSummatory w t at ha
  rw [hi] at ha
  simpa only [arithmeticSummatory, Real.rpow_neg_one, div_eq_mul_inv,
    mul_comm, sub_neg_eq_add] using ha

/-- The exact signed finite Abel identity with both boundary terms retained. -/
theorem reciprocalSummatory_difference_abel (w : ℕ → ℝ) (hw0 : w 0 = 0)
    {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    arithmeticSummatory (fun n => w n / (n : ℝ)) x -
      arithmeticSummatory (fun n => w n / (n : ℝ)) y =
      x ^ (-1 : ℝ) * arithmeticSummatory w x -
      y ^ (-1 : ℝ) * arithmeticSummatory w y +
        ∫ t in Ioc y x, t ^ (-2 : ℝ) * arithmeticSummatory w t := by
  let g : ℝ → ℝ := fun t => t ^ (-2 : ℝ) * arithmeticSummatory w t
  have hi : IntegrableOn g (Ioc 1 x) := by
    exact (integrableOn_mul_sum_Icc w (m := 0) (by norm_num : (0 : ℝ) ≤ 1)
      (rpowContinuous (-2) x).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hi1y : IntervalIntegrable g volume 1 y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy]
    exact hi.mono_set (fun t ht => ⟨ht.1, ht.2.trans hyx⟩)
  have hiyx : IntervalIntegrable g volume y x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hyx]
    exact hi.mono_set (fun t ht => ⟨lt_of_le_of_lt hy ht.1, ht.2⟩)
  have he := intervalIntegral.integral_add_adjacent_intervals hi1y hiyx
  rw [intervalIntegral.integral_of_le hy, intervalIntegral.integral_of_le hyx,
    intervalIntegral.integral_of_le (hy.trans hyx)] at he
  rw [reciprocalSummatory_abel w hw0, reciprocalSummatory_abel w hw0]
  dsimp [g] at he
  linarith

/-- A decreasing secondary profile survives reciprocal Abel summation.
The signed prefix is controlled before taking any absolute coefficient sum. -/
theorem reciprocalSummatory_difference_bound_of_profile
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (L : ℝ → ℝ)
    {B a x y : ℝ} (hB : 0 ≤ B) (ha : a < 1)
    (hy : 1 ≤ y) (hyx : y ≤ x)
    (hL : ∀ t : ℝ, 1 ≤ t → 0 ≤ L t)
    (hLanti : AntitoneOn L (Ici 1))
    (hP : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory w t| ≤ B * t ^ a * L t) :
    |arithmeticSummatory (fun n => w n / (n : ℝ)) x -
      arithmeticSummatory (fun n => w n / (n : ℝ)) y| ≤
      (2 + 1 / (1-a)) * B * y ^ (a-1) * L y := by
  have hy0 : 0 < y := by linarith
  have hp : 0 < 1-a := by linarith
  have hboundary (t : ℝ) (ht : y ≤ t) :
      |t ^ (-1 : ℝ) * arithmeticSummatory w t| ≤
        B * y ^ (a-1) * L y := by
    have ht0 : 0 < t := hy0.trans_le ht
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc
      _ ≤ t ^ (-1 : ℝ) * (B * t^a * L t) :=
        mul_le_mul_of_nonneg_left (hP t (hy.trans ht)) (Real.rpow_nonneg ht0.le _)
      _ = B * t^(a-1) * L t := by
        rw [show t ^ (-1 : ℝ) * (B * t^a * L t) =
          B * (t^(-1 : ℝ) * t^a) * L t by ring, ← Real.rpow_add ht0,
          show (-1 : ℝ)+a = a-1 by ring]
      _ ≤ _ := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hy0 ht (by linarith)) hB
        · exact hLanti hy (hy.trans ht) ht
        · exact hL t (hy.trans ht)
        · positivity
  have hi : IntegrableOn
      (fun t => t ^ (-2 : ℝ) * arithmeticSummatory w t) (Ioc y x) := by
    apply (integrableOn_mul_sum_Icc w (m := 0) (by norm_num : (0 : ℝ) ≤ 1)
      (rpowContinuous (-2) x).integrableOn_Icc).mono_set
    intro t ht
    exact ⟨hy.trans ht.1.le, ht.2⟩
  have hpow : IntegrableOn (fun t : ℝ => t ^ (a-2)) (Ioi y) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hy0
  have hpowint : (∫ t in Ioi y, t ^ (a-2)) = y^(a-1)/(1-a) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hy0]
    rw [show a-2+1 = a-1 by ring]
    field_simp [ne_of_lt (show a-1 < 0 by linarith), ne_of_gt hp]
    ring
  have hIntBound : |∫ t in Ioc y x,
      t ^ (-2 : ℝ) * arithmeticSummatory w t| ≤
        (1/(1-a)) * B * y ^ (a-1) * L y := by
    calc
      _ ≤ ∫ t in Ioc y x, |t ^ (-2 : ℝ) * arithmeticSummatory w t| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioc y x, (B * L y) * t ^ (a-2) := by
        apply integral_mono_ae hi.abs
          ((hpow.mono_set (fun t ht => ht.1)).const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 < t := hy0.trans ht.1
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        calc
          _ ≤ t ^ (-2 : ℝ) * (B * t^a * L t) :=
            mul_le_mul_of_nonneg_left (hP t (hy.trans ht.1.le))
              (Real.rpow_nonneg ht0.le _)
          _ = B * t ^ (a-2) * L t := by
            rw [show t ^ (-2 : ℝ) * (B * t^a * L t) =
              B * (t^(-2 : ℝ) * t^a) * L t by ring, ← Real.rpow_add ht0,
              show (-2 : ℝ)+a = a-2 by ring]
          _ ≤ _ := by
            have h := mul_le_mul_of_nonneg_left
              (hLanti hy (hy.trans ht.1.le) ht.1.le)
              (mul_nonneg hB (Real.rpow_nonneg ht0.le (a-2)))
            nlinarith
      _ ≤ ∫ t in Ioi y, (B * L y) * t ^ (a-2) := by
        apply setIntegral_mono_set (hpow.const_mul _)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (mul_nonneg hB (hL y hy))
            (Real.rpow_nonneg (le_of_lt (hy0.trans ht)) _)
        · exact Filter.Eventually.of_forall (fun t ht => ht.1)
      _ = _ := by rw [integral_const_mul, hpowint]; ring
  rw [reciprocalSummatory_difference_abel w hw0 hy hyx]
  have htri := abs_add_le
    (x ^ (-1 : ℝ) * arithmeticSummatory w x -
      y ^ (-1 : ℝ) * arithmeticSummatory w y)
    (∫ t in Ioc y x, t ^ (-2 : ℝ) * arithmeticSummatory w t)
  have hsub := abs_sub_le
    (x ^ (-1 : ℝ) * arithmeticSummatory w x) 0
    (y ^ (-1 : ℝ) * arithmeticSummatory w y)
  simp only [sub_zero, zero_sub, abs_neg] at hsub
  nlinarith [hboundary x hyx, hboundary y le_rfl]

/-- The density sum need only converge in its natural order. The same
profile controls its tail. No density-tail estimate is assumed. -/
theorem reciprocal_density_tail_bound_of_real_profile
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (L : ℝ → ℝ) (C : ℝ)
    (hdensity : Tendsto
      (fun N => positiveArithmeticPrefix (fun n => w n/(n : ℝ)) N)
      atTop (𝓝 C))
    {B a : ℝ} (hB : 0 ≤ B) (ha : a < 1)
    (hL : ∀ t : ℝ, 1 ≤ t → 0 ≤ L t)
    (hLanti : AntitoneOn L (Ici 1))
    (hP : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory w t| ≤ B * t ^ a * L t)
    {y : ℕ} (hy : 0 < y) :
    |C - positiveArithmeticPrefix (fun n => w n/(n : ℝ)) y| ≤
      (2 + 1 / (1-a)) * B * (y : ℝ) ^ (a-1) * L y := by
  apply le_of_tendsto (hdensity.sub_const
    (positiveArithmeticPrefix (fun n => w n/(n : ℝ)) y)).abs
  filter_upwards [eventually_ge_atTop y] with N hN
  have h := reciprocalSummatory_difference_bound_of_profile w hw0 L
    (x := (N : ℝ)) (y := (y : ℝ)) hB ha (by exact_mod_cast hy) (by exact_mod_cast hN) hL hLanti hP
  simpa only [arithmeticSummatory_eq_positiveArithmeticPrefix
      (fun n => w n/(n : ℝ)) (by simp), Nat.floor_natCast] using h

/-- One signed prefix power estimate supplies the complementary density power. -/
theorem reciprocal_density_tail_bound_of_prefix_power
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun n : ℕ => w (n+1)/((n+1 : ℕ) : ℝ)) C)
    {B a : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a < 1)
    (hP : ∀ n : ℕ, 0 < n → |positiveArithmeticPrefix w n| ≤ B*(n : ℝ)^a)
    {y : ℕ} (hy : 0 < y) :
    |C - positiveArithmeticPrefix (fun n => w n/(n : ℝ)) y| ≤
      ((2 + 1/(1-a))*B) * (y : ℝ)^(a-1) := by
  have hreal (t : ℝ) (ht : 1 ≤ t) :
      |arithmeticSummatory w t| ≤ B * t^a * (1 : ℝ) := by
    have ht0 : 0 ≤ t := by linarith
    have hfloor : 0 < ⌊t⌋₊ := by
      have : 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0).mpr (by exact_mod_cast ht)
      omega
    rw [arithmeticSummatory_eq_positiveArithmeticPrefix w hw0]
    exact (hP _ hfloor).trans (by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (Nat.floor_le ht0) ha) hB)
  simpa only [mul_one] using reciprocal_density_tail_bound_of_real_profile w hw0
    (fun _ => 1) C hdensity.tendsto_sum_nat hB ha1 (fun _ _ => by norm_num)
    (fun _ _ _ _ _ => le_rfl) hreal hy

/-- At the critical power, a single prefix logarithmic saving supplies the
same saving in the density tail. The logarithmic shift is deterministic. -/
theorem reciprocal_density_tail_bound_of_prefix_log
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun n : ℕ => w (n+1)/((n+1 : ℕ) : ℝ)) C)
    {B a b c : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (hc : 0 < c) (hbc : b ≤ a*c)
    (hP : ∀ n : ℕ, 0 < n → |positiveArithmeticPrefix w n| ≤
      B*(n : ℝ)^a/(c+Real.log (n : ℝ))^b)
    {y : ℕ} (hy : 0 < y) :
    |C - positiveArithmeticPrefix (fun n => w n/(n : ℝ)) y| ≤
      ((2 + 1/(1-a))*B) / ((y : ℝ)^(1-a)*(c+Real.log (y : ℝ))^b) := by
  let L : ℝ → ℝ := fun t => (c+Real.log t)^(-b)
  have hL (t : ℝ) (ht : 1 ≤ t) : 0 ≤ L t :=
    Real.rpow_nonneg (powerLog_shift_pos hc ht).le _
  have hanti : AntitoneOn L (Ici 1) := by
    intro x hx z hz hxz
    apply Real.rpow_le_rpow_of_nonpos (powerLog_shift_pos hc hx)
    · linarith [Real.log_le_log (by have hx1 : 1 ≤ x := hx; linarith : 0 < x) hxz]
    · linarith
  have hreal (t : ℝ) (ht : 1 ≤ t) :
      |arithmeticSummatory w t| ≤ B * t^a * L t := by
    have ht0 : 0 ≤ t := by linarith
    have hfloor : 0 < ⌊t⌋₊ := by
      have : 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0).mpr (by exact_mod_cast ht)
      omega
    have hfloor1 : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hfloor
    rw [arithmeticSummatory_eq_positiveArithmeticPrefix w hw0]
    calc
      _ ≤ B * ((⌊t⌋₊ : ℝ)^a/(c+Real.log (⌊t⌋₊ : ℝ))^b) := by
        simpa only [mul_div_assoc] using hP _ hfloor
      _ ≤ B * (t^a/(c+Real.log t)^b) :=
        mul_le_mul_of_nonneg_left
          (powerLogQuotient_monotoneOn hc ha hbc hfloor1 ht (Nat.floor_le ht0)) hB
      _ = _ := by
        dsimp [L]
        rw [Real.rpow_neg (powerLog_shift_pos hc ht).le]
        ring
  have h := reciprocal_density_tail_bound_of_real_profile w hw0 L C
    hdensity.tendsto_sum_nat hB ha1 hL hanti hreal hy
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  convert h using 1
  dsimp [L]
  rw [show a-1 = -(1-a) by ring, Real.rpow_neg hy0.le,
    Real.rpow_neg (powerLog_shift_pos hc hy1).le]
  ring

end RiemannResearch.Analysis
