/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.WeightedMertensTransfer

/-! Arbitrary natural logarithmic powers are preserved by signed Abel transfer.
The shift 6+4k makes the comparison derivative at least one quarter of the
kernel on x≥1. The resulting prefix constant is three, independently of k. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis

def logPowerShift (k : ℕ) : ℝ := 6 + 4 * (k : ℝ)

theorem shiftedLogPower_pos (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    0 < logPowerShift k + Real.log x := by
  dsimp [logPowerShift]
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hl := Real.log_nonneg hx
  linarith

def shiftedLogPowerProfile (k : ℕ) (x : ℝ) : ℝ := (logPowerShift k + Real.log x) ^ (-(k : ℝ))
def halfLogPowerPrimitive (k : ℕ) (x : ℝ) : ℝ := x ^ (1 / 2 : ℝ) * (shiftedLogPowerProfile k) x
def halfLogPowerKernel (k : ℕ) (x : ℝ) : ℝ := x ^ (-1 / 2 : ℝ) * (shiftedLogPowerProfile k) x
def halfLogPowerDerivative (k : ℕ) (x : ℝ) : ℝ :=
  (halfLogPowerKernel k) x * (1 / 2 - (k : ℝ) / (logPowerShift k + Real.log x))

theorem hasDerivAt_halfLogPowerPrimitive (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (halfLogPowerPrimitive k) ((halfLogPowerDerivative k) x) x := by
  have hx0 : 0 < x := by linarith
  have hL := shiftedLogPower_pos k hx
  have h1 := Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl hx0.ne')
  have h2 := ((Real.hasDerivAt_log hx0.ne').const_add (logPowerShift k)).rpow_const
    (p := (-(k : ℝ))) (Or.inl hL.ne')
  have hraw := h1.mul h2
  change HasDerivAt (halfLogPowerPrimitive k) _ x at hraw
  convert hraw using 1
  dsimp [halfLogPowerDerivative, halfLogPowerKernel, shiftedLogPowerProfile]
  rw [Real.rpow_sub_one hx0.ne', Real.rpow_sub_one hL.ne']
  have he : x ^ (-1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) / x := by
    rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num,
      Real.rpow_sub_one hx0.ne']
  rw [he]
  field_simp [hx0.ne', hL.ne']
  <;> ring

theorem halfLogPowerKernel_le_four_derivative (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (halfLogPowerKernel k) x ≤ 4 * (halfLogPowerDerivative k) x := by
  have hL := shiftedLogPower_pos k hx
  have hLk : 4 * (k : ℝ) ≤ logPowerShift k + Real.log x := by
    dsimp [logPowerShift]
    linarith [Real.log_nonneg hx]
  have hq : (k : ℝ) / (logPowerShift k + Real.log x) ≤ 1 / 4 := by
    apply (div_le_iff₀ hL).2
    linarith
  have hk : 0 ≤ (halfLogPowerKernel k) x := by
    unfold halfLogPowerKernel shiftedLogPowerProfile
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg hL.le _)
  unfold halfLogPowerDerivative
  nlinarith

/-- The logarithmic half-power profile increases on the full arithmetic range. -/
theorem halfLogPowerPrimitive_monotoneOn (k : ℕ) : MonotoneOn (halfLogPowerPrimitive k) (Set.Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (1 : ℝ))
  · intro x hx
    exact ((hasDerivAt_halfLogPowerPrimitive k) hx).continuousAt.continuousWithinAt
  · intro x hx
    exact ((hasDerivAt_halfLogPowerPrimitive k) (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hx1 : 1 ≤ x := interior_subset hx
    have h := (halfLogPowerKernel_le_four_derivative k) hx1
    have hk : 0 ≤ (halfLogPowerKernel k) x := by
      unfold halfLogPowerKernel shiftedLogPowerProfile
      exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (shiftedLogPower_pos k hx1).le _)
    linarith

theorem halfLogPowerPrimitive_eq_sqrt_div (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (halfLogPowerPrimitive k) x = Real.sqrt x / (logPowerShift k + Real.log x) ^ (k : ℝ) := by
  unfold halfLogPowerPrimitive shiftedLogPowerProfile
  rw [← Real.sqrt_eq_rpow, Real.rpow_neg (shiftedLogPower_pos k hx).le]
  rfl

private theorem continuousOn_rpow_above_one (k : ℕ) (r b : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ r) (Icc 1 b) := by
  apply ContinuousOn.rpow_const continuousOn_id
  intro x hx
  exact Or.inl (show x ≠ 0 by linarith [hx.1])

private theorem continuousOn_shiftedLogPowerProfile (k : ℕ) (b : ℝ) :
    ContinuousOn (shiftedLogPowerProfile k) (Icc 1 b) := by
  apply ContinuousOn.rpow_const
    ((continuousOn_const).add (continuousOn_id.log (fun x hx => by
      change x ≠ 0
      linarith [hx.1])))
  intro x hx
  exact Or.inl (shiftedLogPower_pos k hx.1).ne'

private theorem continuousOn_halfLogPowerKernel (k : ℕ) (b : ℝ) :
    ContinuousOn (halfLogPowerKernel k) (Icc 1 b) :=
  ((continuousOn_rpow_above_one k) _ _).mul ((continuousOn_shiftedLogPowerProfile k) _)

private theorem continuousOn_halfLogPowerDerivative (k : ℕ) (b : ℝ) :
    ContinuousOn (halfLogPowerDerivative k) (Icc 1 b) := by
  apply ((continuousOn_halfLogPowerKernel k) b).mul
  apply continuousOn_const.sub
  apply continuousOn_const.div
  · exact continuousOn_const.add (continuousOn_id.log (fun x hx => by
      change x ≠ 0
      linarith [hx.1]))
  · intro x hx
    exact (shiftedLogPower_pos k hx.1).ne'

/-- A uniform comparison for the borderline logarithmic kernel. -/
theorem integral_halfLogPowerKernel_le (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Ioc 1 x, (halfLogPowerKernel k) t) ≤ 4 * (halfLogPowerPrimitive k) x := by
  have hI : IntervalIntegrable (halfLogPowerDerivative k) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact (continuousOn_halfLogPowerDerivative k) x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 1) (b := x) (f := (halfLogPowerPrimitive k)) (f' := (halfLogPowerDerivative k))
    (fun t ht => (hasDerivAt_halfLogPowerPrimitive k) (by
      rw [uIcc_of_le hx] at ht
      exact ht.1)) hI
  have hm : (∫ t in Ioc 1 x, (halfLogPowerKernel k) t) ≤
      ∫ t in Ioc 1 x, 4 * (halfLogPowerDerivative k) t := by
    apply integral_mono_ae
      (((continuousOn_halfLogPowerKernel k) x).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((((continuousOn_halfLogPowerDerivative k) x).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self).const_mul 4)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (halfLogPowerKernel_le_four_derivative k) ht.1.le
  rw [intervalIntegral.integral_of_le hx] at hFTC
  rw [integral_const_mul, hFTC] at hm
  have h0 : 0 ≤ (halfLogPowerPrimitive k) 1 := by
    unfold halfLogPowerPrimitive shiftedLogPowerProfile logPowerShift
    positivity
  linarith


/-- A Mertens bound with any real signed coefficients transfers to the
half-damped prefix with an explicit factor three. -/
theorem halfWeightedPrefix_log_power_bound (k : ℕ) (c : ℕ → ℝ) (hc : c 0 = 0)
    {B x : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x)
    (hM : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory c t| ≤ B * t * (shiftedLogPowerProfile k) t) :
    |halfWeightedPrefix c x| ≤ 3 * B * (halfLogPowerPrimitive k) x := by
  have hx0 : 0 < x := by linarith
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hboundary : |x ^ (-1 / 2 : ℝ) * arithmeticSummatory c x| ≤
      B * (halfLogPowerPrimitive k) x := by
    rw [abs_mul, abs_of_nonneg hxp]
    calc
      _ ≤ x ^ (-1 / 2 : ℝ) * (B * x * (shiftedLogPowerProfile k) x) :=
        mul_le_mul_of_nonneg_left (hM x hx) hxp
      _ = _ := by
        have hp : x ^ (-1 / 2 : ℝ) * x = x ^ (1 / 2 : ℝ) := by
          calc
            _ = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hx0]; norm_num
        dsimp [halfLogPowerPrimitive]
        calc
          _ = B * (x ^ (-1 / 2 : ℝ) * x) * (shiftedLogPowerProfile k) x := by ring
          _ = _ := by rw [hp]; ring
  have hInt : IntegrableOn
      (fun t => t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t) (Ioc 1 x) := by
    exact (integrableOn_mul_sum_Icc c (m := 0) (by norm_num : (0 : ℝ) ≤ 1)
      ((continuousOn_rpow_above_one k) (-3 / 2) x).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
  have hpoint (t : ℝ) (ht : t ∈ Ioc 1 x) :
      |t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| ≤ B * (halfLogPowerKernel k) t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have htp : 0 ≤ t ^ (-3 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
    rw [abs_mul, abs_of_nonneg htp]
    calc
      _ ≤ t ^ (-3 / 2 : ℝ) * (B * t * (shiftedLogPowerProfile k) t) :=
        mul_le_mul_of_nonneg_left (hM t ht.1.le) htp
      _ = _ := by
        have hp : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
          calc
            _ = t ^ (-3 / 2 : ℝ) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add ht0]; norm_num
        unfold halfLogPowerKernel
        calc
          _ = B * (t ^ (-3 / 2 : ℝ) * t) * (shiftedLogPowerProfile k) t := by ring
          _ = _ := by rw [hp]; ring
  have habsI : |∫ t in Ioc 1 x,
      t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| ≤
        4 * B * (halfLogPowerPrimitive k) x := by
    calc
      _ ≤ ∫ t in Ioc 1 x, |t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioc 1 x, B * (halfLogPowerKernel k) t := by
        apply integral_mono_ae hInt.abs
          ((((continuousOn_halfLogPowerKernel k) x).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self).const_mul B)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpoint t ht
      _ = B * ∫ t in Ioc 1 x, (halfLogPowerKernel k) t := integral_const_mul _ _
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left ((integral_halfLogPowerKernel_le k) hx) hB
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
