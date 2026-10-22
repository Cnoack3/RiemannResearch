/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Elementary Abel transfer for the half-damped endpoint. The logarithmic shift
6 makes the comparison derivative positive on the full range x ≥ 1.
The statements are for arbitrary real coefficients, not only the Möbius function.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis

def shiftedLogProfile (x : ℝ) : ℝ := (6 + Real.log x) ^ (-3 / 2 : ℝ)
def halfLogPrimitive (x : ℝ) : ℝ := x ^ (1 / 2 : ℝ) * shiftedLogProfile x
def halfLogKernel (x : ℝ) : ℝ := x ^ (-1 / 2 : ℝ) * shiftedLogProfile x
def halfLogDerivative (x : ℝ) : ℝ :=
  halfLogKernel x * (1 / 2 - (3 / 2 : ℝ) / (6 + Real.log x))

theorem shiftedLog_pos {x : ℝ} (hx : 1 ≤ x) : 0 < 6 + Real.log x := by
  have := Real.log_nonneg hx
  linarith

theorem hasDerivAt_halfLogPrimitive {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt halfLogPrimitive (halfLogDerivative x) x := by
  have hx0 : 0 < x := by linarith
  have hL := shiftedLog_pos hx
  have h1 := Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl hx0.ne')
  have h2 := ((Real.hasDerivAt_log hx0.ne').const_add 6).rpow_const
    (p := (-3 / 2 : ℝ)) (Or.inl hL.ne')
  have hraw := h1.mul h2
  change HasDerivAt halfLogPrimitive _ x at hraw
  convert hraw using 1
  dsimp [halfLogDerivative, halfLogKernel, shiftedLogProfile]
  rw [Real.rpow_sub_one hx0.ne', Real.rpow_sub_one hL.ne']
  have he : x ^ (-1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) / x := by
    rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num,
      Real.rpow_sub_one hx0.ne']
  rw [he]
  field_simp [hx0.ne', hL.ne']
  <;> ring

theorem halfLogKernel_le_four_derivative {x : ℝ} (hx : 1 ≤ x) :
    halfLogKernel x ≤ 4 * halfLogDerivative x := by
  have hL := shiftedLog_pos hx
  have hL6 : 6 ≤ 6 + Real.log x := by linarith [Real.log_nonneg hx]
  have hq : (3 / 2 : ℝ) / (6 + Real.log x) ≤ 1 / 4 := by
    apply (div_le_iff₀ hL).2
    linarith
  have hk : 0 ≤ halfLogKernel x := by
    unfold halfLogKernel shiftedLogProfile
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg hL.le _)
  unfold halfLogDerivative
  nlinarith

/-- The logarithmic half-power profile increases on the full arithmetic range. -/
theorem halfLogPrimitive_monotoneOn : MonotoneOn halfLogPrimitive (Set.Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (1 : ℝ))
  · intro x hx
    exact (hasDerivAt_halfLogPrimitive hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_halfLogPrimitive (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hx1 : 1 ≤ x := interior_subset hx
    have h := halfLogKernel_le_four_derivative hx1
    have hk : 0 ≤ halfLogKernel x := by
      unfold halfLogKernel shiftedLogProfile
      exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (shiftedLog_pos hx1).le _)
    linarith

theorem halfLogPrimitive_eq_sqrt_div {x : ℝ} (hx : 1 ≤ x) :
    halfLogPrimitive x = Real.sqrt x / (6 + Real.log x) ^ (3 / 2 : ℝ) := by
  unfold halfLogPrimitive shiftedLogProfile
  rw [← Real.sqrt_eq_rpow, show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring,
    Real.rpow_neg (shiftedLog_pos hx).le]
  rfl

private theorem continuousOn_rpow_above_one (r b : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ r) (Icc 1 b) := by
  apply ContinuousOn.rpow_const continuousOn_id
  intro x hx
  exact Or.inl (show x ≠ 0 by linarith [hx.1])

private theorem continuousOn_shiftedLogProfile (b : ℝ) :
    ContinuousOn shiftedLogProfile (Icc 1 b) := by
  apply ContinuousOn.rpow_const
    ((continuousOn_const).add (continuousOn_id.log (fun x hx => by
      change x ≠ 0
      linarith [hx.1])))
  intro x hx
  exact Or.inl (shiftedLog_pos hx.1).ne'

private theorem continuousOn_halfLogKernel (b : ℝ) :
    ContinuousOn halfLogKernel (Icc 1 b) :=
  (continuousOn_rpow_above_one _ _).mul (continuousOn_shiftedLogProfile _)

private theorem continuousOn_halfLogDerivative (b : ℝ) :
    ContinuousOn halfLogDerivative (Icc 1 b) := by
  apply (continuousOn_halfLogKernel b).mul
  apply continuousOn_const.sub
  apply continuousOn_const.div
  · exact continuousOn_const.add (continuousOn_id.log (fun x hx => by
      change x ≠ 0
      linarith [hx.1]))
  · intro x hx
    exact (shiftedLog_pos hx.1).ne'

/-- A uniform comparison for the borderline logarithmic kernel. -/
theorem integral_halfLogKernel_le {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Ioc 1 x, halfLogKernel t) ≤ 4 * halfLogPrimitive x := by
  have hI : IntervalIntegrable halfLogDerivative volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact continuousOn_halfLogDerivative x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 1) (b := x) (f := halfLogPrimitive) (f' := halfLogDerivative)
    (fun t ht => hasDerivAt_halfLogPrimitive (by
      rw [uIcc_of_le hx] at ht
      exact ht.1)) hI
  have hm : (∫ t in Ioc 1 x, halfLogKernel t) ≤
      ∫ t in Ioc 1 x, 4 * halfLogDerivative t := by
    apply integral_mono_ae
      ((continuousOn_halfLogKernel x).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (((continuousOn_halfLogDerivative x).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self).const_mul 4)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact halfLogKernel_le_four_derivative ht.1.le
  rw [intervalIntegral.integral_of_le hx] at hFTC
  rw [integral_const_mul, hFTC] at hm
  have h0 : 0 ≤ halfLogPrimitive 1 := by
    unfold halfLogPrimitive shiftedLogProfile
    positivity
  linarith

def arithmeticSummatory (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n

def halfWeightedPrefix (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n * (n : ℝ) ^ (-1 / 2 : ℝ)

/-- Exact half-power Abel summation, for arbitrary real coefficients. -/
theorem halfWeightedPrefix_abel (c : ℕ → ℝ) (hc : c 0 = 0) (x : ℝ) :
    halfWeightedPrefix c x = x ^ (-1 / 2 : ℝ) * arithmeticSummatory c x +
      (1 / 2 : ℝ) * ∫ t in Ioc 1 x,
        t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t := by
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :
      HasDerivAt (fun y : ℝ => y ^ (-1 / 2 : ℝ))
        ((-1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ)) t := by
    convert Real.hasDerivAt_rpow_const (x := t) (p := (-1 / 2 : ℝ))
      (Or.inl (ne_of_gt (by linarith [ht.1]))) using 1 <;> norm_num
  have hdc : ContinuousOn (deriv (fun y : ℝ => y ^ (-1 / 2 : ℝ)))
      (Icc 1 x) := by
    apply ((continuousOn_rpow_above_one (-3 / 2) x).const_mul (-1 / 2)).congr
    intro t ht
    exact (hd t ht).deriv
  have ha := sum_mul_eq_sub_integral_mul₀ c hc x
    (fun t ht => (hd t ht).differentiableAt) hdc.integrableOn_Icc
  have hi : (∫ t in Ioc 1 x,
      deriv (fun y : ℝ => y ^ (-1 / 2 : ℝ)) t * arithmeticSummatory c t) =
      (-1 / 2 : ℝ) * ∫ t in Ioc 1 x,
        t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
    ring
  change (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℝ) ^ (-1 / 2 : ℝ) * c n) =
    x ^ (-1 / 2 : ℝ) * arithmeticSummatory c x -
      ∫ t in Ioc 1 x,
        deriv (fun y : ℝ => y ^ (-1 / 2 : ℝ)) t * arithmeticSummatory c t at ha
  rw [hi] at ha
  unfold halfWeightedPrefix
  simp_rw [mul_comm (c _) _]
  linarith

/-- A Mertens bound with any real signed coefficients transfers to the
half-damped prefix with an explicit factor three. -/
theorem halfWeightedPrefix_bound (c : ℕ → ℝ) (hc : c 0 = 0)
    {B x : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x)
    (hM : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory c t| ≤ B * t * shiftedLogProfile t) :
    |halfWeightedPrefix c x| ≤ 3 * B * halfLogPrimitive x := by
  have hx0 : 0 < x := by linarith
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hboundary : |x ^ (-1 / 2 : ℝ) * arithmeticSummatory c x| ≤
      B * halfLogPrimitive x := by
    rw [abs_mul, abs_of_nonneg hxp]
    calc
      _ ≤ x ^ (-1 / 2 : ℝ) * (B * x * shiftedLogProfile x) :=
        mul_le_mul_of_nonneg_left (hM x hx) hxp
      _ = _ := by
        have hp : x ^ (-1 / 2 : ℝ) * x = x ^ (1 / 2 : ℝ) := by
          calc
            _ = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hx0]; norm_num
        dsimp [halfLogPrimitive]
        calc
          _ = B * (x ^ (-1 / 2 : ℝ) * x) * shiftedLogProfile x := by ring
          _ = _ := by rw [hp]; ring
  have hInt : IntegrableOn
      (fun t => t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t) (Ioc 1 x) := by
    exact (integrableOn_mul_sum_Icc c (m := 0) (by norm_num : (0 : ℝ) ≤ 1)
      (continuousOn_rpow_above_one (-3 / 2) x).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
  have hpoint (t : ℝ) (ht : t ∈ Ioc 1 x) :
      |t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| ≤ B * halfLogKernel t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have htp : 0 ≤ t ^ (-3 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
    rw [abs_mul, abs_of_nonneg htp]
    calc
      _ ≤ t ^ (-3 / 2 : ℝ) * (B * t * shiftedLogProfile t) :=
        mul_le_mul_of_nonneg_left (hM t ht.1.le) htp
      _ = _ := by
        have hp : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
          calc
            _ = t ^ (-3 / 2 : ℝ) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add ht0]; norm_num
        unfold halfLogKernel
        calc
          _ = B * (t ^ (-3 / 2 : ℝ) * t) * shiftedLogProfile t := by ring
          _ = _ := by rw [hp]; ring
  have habsI : |∫ t in Ioc 1 x,
      t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| ≤
        4 * B * halfLogPrimitive x := by
    calc
      _ ≤ ∫ t in Ioc 1 x, |t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioc 1 x, B * halfLogKernel t := by
        apply integral_mono_ae hInt.abs
          (((continuousOn_halfLogKernel x).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self).const_mul B)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpoint t ht
      _ = B * ∫ t in Ioc 1 x, halfLogKernel t := integral_const_mul _ _
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left (integral_halfLogKernel_le hx) hB
        nlinarith
  rw [halfWeightedPrefix_abel c hc]
  calc
    _ ≤ |x ^ (-1 / 2 : ℝ) * arithmeticSummatory c x| +
        |(1 / 2 : ℝ) * ∫ t in Ioc 1 x,
          t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul (1 / 2 : ℝ)]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      nlinarith

end RiemannResearch.Analysis
