/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.WeightedMertensTransfer
import RiemannResearch.Analysis.WeightedMertensTail

/-! Signed Abel transfer preserves the optimized stretched scale
((6+log x)*log(6+log x))^β. For β≤1/2 its derivative with respect to log x
is at most two. Thus d≤1/8 leaves the primitive derivative ≥kernel/4. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis

def stretchedLoglogCore (x : ℝ) : ℝ :=
  (6 + Real.log x) * Real.log (6 + Real.log x)

theorem shiftedLog_log_ge_half {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2 : ℝ) ≤ Real.log (6 + Real.log x) := by
  have hL := shiftedLog_pos hx
  have hL6 : 6 ≤ 6 + Real.log x := by linarith [Real.log_nonneg hx]
  have hi : 1 / (6 + Real.log x) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hL).mpr
    linarith
  have h := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 1 / (6 + Real.log x))
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hL.ne',
    Real.log_one, zero_sub] at h
  linarith

theorem stretchedLoglogCore_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < stretchedLoglogCore x := by
  unfold stretchedLoglogCore
  exact mul_pos (shiftedLog_pos hx) (by linarith [shiftedLog_log_ge_half hx])

theorem stretchedLoglogCore_ge_one {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ stretchedLoglogCore x := by
  have hL6 : 6 ≤ 6 + Real.log x := by linarith [Real.log_nonneg hx]
  have hlog := shiftedLog_log_ge_half hx
  unfold stretchedLoglogCore
  have h := mul_le_mul hL6 hlog (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by linarith : 0 ≤ 6 + Real.log x)
  nlinarith

def loglogStretchedProfile (β d x : ℝ) : ℝ :=
  Real.exp (-d * (stretchedLoglogCore x) ^ β)

def halfLoglogStretchedPrimitive (β d x : ℝ) : ℝ :=
  x ^ (1 / 2 : ℝ) * loglogStretchedProfile β d x

def halfLoglogStretchedKernel (β d x : ℝ) : ℝ :=
  x ^ (-1 / 2 : ℝ) * loglogStretchedProfile β d x

def loglogStretchedSlope (β x : ℝ) : ℝ :=
  β * (stretchedLoglogCore x) ^ (β - 1) *
    (Real.log (6 + Real.log x) + 1)

def halfLoglogStretchedDerivative (β d x : ℝ) : ℝ :=
  halfLoglogStretchedKernel β d x * (1 / 2 - d * loglogStretchedSlope β x)

theorem hasDerivAt_stretchedLoglogCore {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt stretchedLoglogCore
      ((Real.log (6 + Real.log x) + 1) / x) x := by
  have hx0 : 0 < x := by linarith
  have hL := shiftedLog_pos hx
  have h1 := (Real.hasDerivAt_log hx0.ne').const_add 6
  have h := h1.mul (h1.log hL.ne')
  change HasDerivAt stretchedLoglogCore _ x at h
  convert h using 1
  field_simp [hx0.ne', hL.ne']
  <;> ring

theorem hasDerivAt_loglogStretchedProfile (β d : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (loglogStretchedProfile β d)
      (loglogStretchedProfile β d x * (-d * loglogStretchedSlope β x / x)) x := by
  have hx0 : 0 < x := by linarith
  have hP := stretchedLoglogCore_pos hx
  have h := (((hasDerivAt_stretchedLoglogCore hx).rpow_const
    (p := β) (Or.inl hP.ne')).const_mul (-d)).exp
  change HasDerivAt (loglogStretchedProfile β d) _ x at h
  convert h using 1
  dsimp [loglogStretchedProfile, loglogStretchedSlope]
  field_simp [hx0.ne']
  <;> ring

theorem hasDerivAt_halfLoglogStretchedPrimitive (β d : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (halfLoglogStretchedPrimitive β d)
      (halfLoglogStretchedDerivative β d x) x := by
  have hx0 : 0 < x := by linarith
  have h1 := Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl hx0.ne')
  have hraw := h1.mul (hasDerivAt_loglogStretchedProfile β d hx)
  change HasDerivAt (halfLoglogStretchedPrimitive β d) _ x at hraw
  convert hraw using 1
  dsimp [halfLoglogStretchedDerivative, halfLoglogStretchedKernel]
  rw [Real.rpow_sub_one hx0.ne']
  have he : x ^ (-1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) / x := by
    rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num,
      Real.rpow_sub_one hx0.ne']
  rw [he]
  field_simp [hx0.ne']
  <;> ring

theorem loglogStretchedSlope_nonneg
    (β : ℝ) (hβ0 : 0 ≤ β) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ loglogStretchedSlope β x := by
  unfold loglogStretchedSlope
  exact mul_nonneg (mul_nonneg hβ0 (Real.rpow_nonneg (stretchedLoglogCore_pos hx).le _))
    (by linarith [shiftedLog_log_ge_half hx])

theorem loglogStretchedSlope_le_two
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 2)
    {x : ℝ} (hx : 1 ≤ x) :
    loglogStretchedSlope β x ≤ 2 := by
  let L := 6 + Real.log x
  let P := stretchedLoglogCore x
  have hL : 0 < L := shiftedLog_pos hx
  have hlog : (1 / 2 : ℝ) ≤ Real.log L := shiftedLog_log_ge_half hx
  have hP : 0 < P := stretchedLoglogCore_pos hx
  have hP1 : 1 ≤ P := stretchedLoglogCore_ge_one hx
  have hlogL : Real.log L ≤ L := by
    linarith [Real.log_le_sub_one_of_pos hL]
  have hsq := Real.sq_sqrt hP.le
  have hs0 := Real.sqrt_nonneg P
  have hs : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hls : Real.log L ≤ Real.sqrt P := by
    have hprod := mul_nonneg (show 0 ≤ Real.log L by linarith)
      (sub_nonneg.mpr hlogL)
    have he : P = L * Real.log L := rfl
    nlinarith
  have hplus : Real.log L + 1 ≤ 3 * Real.sqrt P := by linarith
  have hp0 : 0 ≤ P ^ (β - 1) := Real.rpow_nonneg hP.le _
  have hp : P ^ (β - 1) ≤ 1 / Real.sqrt P := by
    calc
      _ ≤ P ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
      _ = _ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
          Real.rpow_neg hP.le, ← Real.sqrt_eq_rpow, inv_eq_one_div]
  have hps : P ^ (β - 1) * Real.sqrt P ≤ 1 :=
    (le_div_iff₀ hs).mp hp
  have h1 := mul_le_mul_of_nonneg_left hplus (mul_nonneg hβ0 hp0)
  have h2 := mul_le_mul_of_nonneg_left hps hβ0
  change β * P ^ (β - 1) * (Real.log L + 1) ≤ 2
  nlinarith

theorem halfLoglogStretchedKernel_le_four_derivative
    (β d : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 2)
    (hd0 : 0 ≤ d) (hd8 : d ≤ 1 / 8) {x : ℝ} (hx : 1 ≤ x) :
    halfLoglogStretchedKernel β d x ≤ 4 * halfLoglogStretchedDerivative β d x := by
  have hq := mul_le_mul_of_nonneg_left (loglogStretchedSlope_le_two β hβ0 hβ1 hx) hd0
  have hq4 : d * loglogStretchedSlope β x ≤ 1 / 4 := by linarith
  have hk : 0 ≤ halfLoglogStretchedKernel β d x := by
    unfold halfLoglogStretchedKernel loglogStretchedProfile
    positivity
  unfold halfLoglogStretchedDerivative
  nlinarith

theorem halfLoglogStretchedPrimitive_monotoneOn
    (β d : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 2)
    (hd0 : 0 ≤ d) (hd8 : d ≤ 1 / 8) :
    MonotoneOn (halfLoglogStretchedPrimitive β d) (Set.Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (1 : ℝ))
  · intro x hx
    exact (hasDerivAt_halfLoglogStretchedPrimitive β d hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_halfLoglogStretchedPrimitive β d (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hx1 : 1 ≤ x := interior_subset hx
    have h := halfLoglogStretchedKernel_le_four_derivative β d hβ0 hβ1 hd0 hd8 hx1
    have hk : 0 ≤ halfLoglogStretchedKernel β d x := by
      unfold halfLoglogStretchedKernel loglogStretchedProfile
      positivity
    linarith

theorem halfLoglogStretchedPrimitive_eq_sqrt (β d x : ℝ) :
    halfLoglogStretchedPrimitive β d x =
      Real.sqrt x * loglogStretchedProfile β d x := by
  unfold halfLoglogStretchedPrimitive
  rw [← Real.sqrt_eq_rpow]

private theorem continuousOn_rpow_above_one (r b : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ r) (Icc 1 b) := by
  apply ContinuousOn.rpow_const continuousOn_id
  intro x hx
  exact Or.inl (show x ≠ 0 by linarith [hx.1])

private theorem continuousOn_loglogStretchedProfile (β d b : ℝ) :
    ContinuousOn (loglogStretchedProfile β d) (Icc 1 b) := by
  intro x hx
  exact (hasDerivAt_loglogStretchedProfile β d hx.1).continuousAt.continuousWithinAt

private theorem continuousOn_halfLoglogStretchedKernel (β d b : ℝ) :
    ContinuousOn (halfLoglogStretchedKernel β d) (Icc 1 b) :=
  (continuousOn_rpow_above_one _ _).mul (continuousOn_loglogStretchedProfile β d _)

private theorem continuousOn_halfLoglogStretchedDerivative (β d b : ℝ) :
    ContinuousOn (halfLoglogStretchedDerivative β d) (Icc 1 b) := by
  have hL : ContinuousOn (fun x : ℝ => 6 + Real.log x) (Icc 1 b) :=
    continuousOn_const.add (continuousOn_id.log (fun x hx => by
      change x ≠ 0
      linarith [hx.1]))
  have hlogL : ContinuousOn (fun x : ℝ => Real.log (6 + Real.log x)) (Icc 1 b) :=
    hL.log (fun x hx => (shiftedLog_pos hx.1).ne')
  have hP : ContinuousOn stretchedLoglogCore (Icc 1 b) := hL.mul hlogL
  have hp : ContinuousOn (fun x => (stretchedLoglogCore x) ^ (β - 1)) (Icc 1 b) := by
    apply hP.rpow_const
    intro x hx
    exact Or.inl (stretchedLoglogCore_pos hx.1).ne'
  exact (continuousOn_halfLoglogStretchedKernel β d b).mul
    (continuousOn_const.sub (((hp.const_mul β).mul
      (hlogL.add continuousOn_const)).const_mul d))

theorem integral_halfLoglogStretchedKernel_le
    (β d : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 2)
    (hd0 : 0 ≤ d) (hd8 : d ≤ 1 / 8) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Ioc 1 x, halfLoglogStretchedKernel β d t) ≤
      4 * halfLoglogStretchedPrimitive β d x := by
  have hI : IntervalIntegrable (halfLoglogStretchedDerivative β d) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact continuousOn_halfLoglogStretchedDerivative β d x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 1) (b := x) (f := halfLoglogStretchedPrimitive β d)
    (f' := halfLoglogStretchedDerivative β d)
    (fun t ht => hasDerivAt_halfLoglogStretchedPrimitive β d (by
      rw [uIcc_of_le hx] at ht
      exact ht.1)) hI
  have hm : (∫ t in Ioc 1 x, halfLoglogStretchedKernel β d t) ≤
      ∫ t in Ioc 1 x, 4 * halfLoglogStretchedDerivative β d t := by
    apply integral_mono_ae
      ((continuousOn_halfLoglogStretchedKernel β d x).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (((continuousOn_halfLoglogStretchedDerivative β d x).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self).const_mul 4)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact halfLoglogStretchedKernel_le_four_derivative β d hβ0 hβ1 hd0 hd8 ht.1.le
  rw [intervalIntegral.integral_of_le hx] at hFTC
  rw [integral_const_mul, hFTC] at hm
  have h0 : 0 ≤ halfLoglogStretchedPrimitive β d 1 := by
    unfold halfLoglogStretchedPrimitive loglogStretchedProfile
    positivity
  linarith

/-- A Mertens bound with any real signed coefficients transfers to the
half-damped prefix with an explicit factor three. -/
theorem halfWeightedPrefix_loglog_stretched_bound
    (β d : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 2)
    (hd0 : 0 ≤ d) (hd8 : d ≤ 1 / 8) (c : ℕ → ℝ) (hc : c 0 = 0)
    {B x : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x)
    (hM : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory c t| ≤ B * t * loglogStretchedProfile β d t) :
    |halfWeightedPrefix c x| ≤ 3 * B * halfLoglogStretchedPrimitive β d x := by
  have hx0 : 0 < x := by linarith
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hboundary : |x ^ (-1 / 2 : ℝ) * arithmeticSummatory c x| ≤
      B * halfLoglogStretchedPrimitive β d x := by
    rw [abs_mul, abs_of_nonneg hxp]
    calc
      _ ≤ x ^ (-1 / 2 : ℝ) * (B * x * loglogStretchedProfile β d x) :=
        mul_le_mul_of_nonneg_left (hM x hx) hxp
      _ = _ := by
        have hp : x ^ (-1 / 2 : ℝ) * x = x ^ (1 / 2 : ℝ) := by
          calc
            _ = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hx0]; norm_num
        dsimp [halfLoglogStretchedPrimitive]
        calc
          _ = B * (x ^ (-1 / 2 : ℝ) * x) * loglogStretchedProfile β d x := by ring
          _ = _ := by rw [hp]; ring
  have hInt : IntegrableOn
      (fun t => t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t) (Ioc 1 x) := by
    exact (integrableOn_mul_sum_Icc c (m := 0) (by norm_num : (0 : ℝ) ≤ 1)
      (continuousOn_rpow_above_one (-3 / 2) x).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
  have hpoint (t : ℝ) (ht : t ∈ Ioc 1 x) :
      |t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| ≤ B * halfLoglogStretchedKernel β d t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have htp : 0 ≤ t ^ (-3 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
    rw [abs_mul, abs_of_nonneg htp]
    calc
      _ ≤ t ^ (-3 / 2 : ℝ) * (B * t * loglogStretchedProfile β d t) :=
        mul_le_mul_of_nonneg_left (hM t ht.1.le) htp
      _ = _ := by
        have hp : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
          calc
            _ = t ^ (-3 / 2 : ℝ) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add ht0]; norm_num
        unfold halfLoglogStretchedKernel
        calc
          _ = B * (t ^ (-3 / 2 : ℝ) * t) * loglogStretchedProfile β d t := by ring
          _ = _ := by rw [hp]; ring
  have habsI : |∫ t in Ioc 1 x,
      t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| ≤
        4 * B * halfLoglogStretchedPrimitive β d x := by
    calc
      _ ≤ ∫ t in Ioc 1 x, |t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioc 1 x, B * halfLoglogStretchedKernel β d t := by
        apply integral_mono_ae hInt.abs
          (((continuousOn_halfLoglogStretchedKernel β d x).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self).const_mul B)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpoint t ht
      _ = B * ∫ t in Ioc 1 x, halfLoglogStretchedKernel β d t := integral_const_mul _ _
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left (integral_halfLoglogStretchedKernel_le β d hβ0 hβ1 hd0 hd8 hx) hB
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



theorem loglogStretchedProfile_antitone
    (β d : ℝ) (hβ0 : 0 ≤ β) (hd0 : 0 ≤ d)
    {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    loglogStretchedProfile β d x ≤ loglogStretchedProfile β d y := by
  have hx : 1 ≤ x := hy.trans hyx
  have hL : 6 + Real.log y ≤ 6 + Real.log x := by
    linarith [Real.log_le_log (by linarith : 0 < y) hyx]
  have hlog : Real.log (6 + Real.log y) ≤ Real.log (6 + Real.log x) :=
    Real.log_le_log (shiftedLog_pos hy) hL
  have hP : stretchedLoglogCore y ≤ stretchedLoglogCore x := by
    unfold stretchedLoglogCore
    exact mul_le_mul hL hlog (by linarith [shiftedLog_log_ge_half hy])
      (shiftedLog_pos hx).le
  have hp := Real.rpow_le_rpow (stretchedLoglogCore_pos hy).le hP hβ0
  unfold loglogStretchedProfile
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A finite reciprocal-density tail estimate. The constant five permits the
right boundary to be controlled uniformly before taking any infinite limit. -/
theorem threeHalfWeightedPrefix_loglog_stretched_difference_bound
    (β d : ℝ) (hβ0 : 0 ≤ β) (hd0 : 0 ≤ d) (c : ℕ → ℝ) (hc : c 0 = 0)
    {B x y : ℝ} (hB : 0 ≤ B) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hM : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory c t| ≤ B * t * loglogStretchedProfile β d t) :
    |threeHalfWeightedPrefix c x - threeHalfWeightedPrefix c y| ≤
      5 * B * y ^ (-1 / 2 : ℝ) * loglogStretchedProfile β d y := by
  have hy0 : 0 < y := by linarith
  have hprof : 0 ≤ loglogStretchedProfile β d y := by
    unfold loglogStretchedProfile
    positivity
  have hboundary (t : ℝ) (ht : y ≤ t) :
      |t ^ (-3 / 2 : ℝ) * arithmeticSummatory c t| ≤
        B * y ^ (-1 / 2 : ℝ) * loglogStretchedProfile β d y := by
    have ht0 : 0 < t := hy0.trans_le ht
    have hp : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
      calc
        _ = t ^ (-3 / 2 : ℝ) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add ht0]; norm_num
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc
      _ ≤ t ^ (-3 / 2 : ℝ) * (B * t * loglogStretchedProfile β d t) :=
        mul_le_mul_of_nonneg_left (hM t (hy.trans ht)) (Real.rpow_nonneg ht0.le _)
      _ = B * t ^ (-1 / 2 : ℝ) * loglogStretchedProfile β d t := by
        calc
          _ = B * (t ^ (-3 / 2 : ℝ) * t) * loglogStretchedProfile β d t := by ring
          _ = _ := by rw [hp]
      _ ≤ _ := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hy0 ht (by norm_num)) hB
        · exact loglogStretchedProfile_antitone β d hβ0 hd0 hy ht
        · unfold loglogStretchedProfile
          positivity
        · positivity
  have hi : IntegrableOn
      (fun t => t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t) (Ioc y x) := by
    apply (integrableOn_mul_sum_Icc c (m := 0) (by norm_num : (0 : ℝ) ≤ 1)
      (continuousOn_rpow_above_one (-5 / 2) x).integrableOn_Icc).mono_set
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
        2 * B * y ^ (-1 / 2 : ℝ) * loglogStretchedProfile β d y := by
    calc
      _ ≤ ∫ t in Ioc y x, |t ^ (-5 / 2 : ℝ) * arithmeticSummatory c t| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioc y x, (B * loglogStretchedProfile β d y) * t ^ (-3 / 2 : ℝ) := by
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
          _ ≤ t ^ (-5 / 2 : ℝ) * (B * t * loglogStretchedProfile β d t) :=
            mul_le_mul_of_nonneg_left (hM t (hy.trans ht.1.le))
              (Real.rpow_nonneg ht0.le _)
          _ = B * t ^ (-3 / 2 : ℝ) * loglogStretchedProfile β d t := by
            calc
              _ = B * (t ^ (-5 / 2 : ℝ) * t) * loglogStretchedProfile β d t := by ring
              _ = _ := by rw [hp]
          _ ≤ _ := by
            have := mul_le_mul_of_nonneg_left (loglogStretchedProfile_antitone β d hβ0 hd0 hy ht.1.le)
              (mul_nonneg hB (Real.rpow_nonneg ht0.le (-3 / 2)))
            nlinarith
      _ ≤ ∫ t in Ioi y, (B * loglogStretchedProfile β d y) * t ^ (-3 / 2 : ℝ) := by
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


/-- The infinite density tail inherits the same logarithmic saving as the
summatory function. Absolute summability of the density series is explicit. -/
theorem threeHalfWeightedPrefix_loglog_stretched_tail_bound
    (β d : ℝ) (hβ0 : 0 ≤ β) (hd0 : 0 ≤ d) (c : ℕ → ℝ) (hc : c 0 = 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory c t| ≤ B * t * loglogStretchedProfile β d t)
    (hs : Summable (fun n : ℕ => c n * (n : ℝ) ^ (-3 / 2 : ℝ)))
    {y : ℕ} (hy : 1 ≤ y) :
    |(∑' n : ℕ, c n * (n : ℝ) ^ (-3 / 2 : ℝ)) - threeHalfWeightedPrefix c y| ≤
      5 * B * (y : ℝ) ^ (-1 / 2 : ℝ) * loglogStretchedProfile β d y := by
  apply le_of_tendsto ((threeHalfWeightedPrefix_tendsto c hs).sub_const
    (threeHalfWeightedPrefix c y)).abs
  filter_upwards [eventually_ge_atTop y] with N hN
  exact threeHalfWeightedPrefix_loglog_stretched_difference_bound β d hβ0 hd0 c hc hB
    (by exact_mod_cast hy) (by exact_mod_cast hN) hM



end RiemannResearch.Analysis
