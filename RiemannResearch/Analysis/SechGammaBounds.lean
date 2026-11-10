/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! Elementary analytic estimates for the kernel in MontgomeryGammaAudit20261110.md.
Source: user-provided argument, Sections 4--5. No zero-statistic hypothesis is used. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.SechGammaBounds

def kernel (t : ℝ) : ℝ := 1 / (2 * Real.sinh t) + 1 / (4 * Real.cosh (t / 2)^2)
def first (t : ℝ) : ℝ := -Real.cosh t / (2 * Real.sinh t ^ 2) -
  Real.sinh (t / 2) / (4 * Real.cosh (t / 2)^3)
def second (t : ℝ) : ℝ := 1 / Real.sinh t ^ 3 + 1 / (2 * Real.sinh t) +
  1 / (4 * Real.cosh (t / 2)^2) * (1 - 3 / (2 * Real.cosh (t / 2)^2))

theorem one_add_quadratic_le_cosh {x : ℝ} (hx : 0 ≤ x) :
    1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hd (t : ℝ) : HasDerivAt (fun y : ℝ => Real.cosh y - y ^ 2/2)
      (Real.sinh t - t) t := by
    convert! (Real.hasDerivAt_cosh t).sub (((hasDerivAt_id t).pow 2).div_const 2) using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring
  have hm : MonotoneOn (fun y : ℝ => Real.cosh y - y ^ 2/2) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    · intro t ht; exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      exact sub_nonneg.mpr (Real.self_le_sinh_iff.mpr (interior_subset ht))
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) hx hx
  norm_num at h
  linarith

theorem cubic_le_sinh {x : ℝ} (hx : 0 ≤ x) :
    x ^ 3 ≤ 6 * Real.sinh x := by
  have hd (t : ℝ) : HasDerivAt (fun y : ℝ => Real.sinh y - y ^ 3/6)
      (Real.cosh t - t ^ 2/2) t := by
    convert! (Real.hasDerivAt_sinh t).sub (((hasDerivAt_id t).pow 3).div_const 6) using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
    ring
  have hm : MonotoneOn (fun y : ℝ => Real.sinh y - y ^ 3/6) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    · intro t ht; exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      have h := one_add_quadratic_le_cosh (interior_subset ht)
      linarith
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) hx hx
  norm_num at h
  linarith

theorem hasDerivAt_kernel {t : ℝ} (ht : 0 < t) : HasDerivAt kernel (first t) t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have hc : Real.cosh (t / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hd := (Real.hasDerivAt_cosh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
  convert! ((hasDerivAt_const t (1:ℝ)).div ((Real.hasDerivAt_sinh t).const_mul 2)
    (mul_ne_zero (by norm_num) hs)).add
    ((hasDerivAt_const t (1:ℝ)).div ((hd.pow 2).const_mul 4)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hc))) using 1
  simp only [first, Function.comp_apply, id_eq, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

theorem hasDerivAt_first {t : ℝ} (ht : 0 < t) : HasDerivAt first (second t) t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have hc : Real.cosh (t / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hdc := (Real.hasDerivAt_cosh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
  have hds := (Real.hasDerivAt_sinh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
  convert! (((Real.hasDerivAt_cosh t).neg).div (((Real.hasDerivAt_sinh t).pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hs))).sub
    (hds.div ((hdc.pow 3).const_mul 4)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hc))) using 1
  simp only [second, Function.comp_apply, id_eq, Pi.pow_apply, Pi.neg_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have h1 : Real.cosh t ^ 2 = Real.sinh t ^ 2+1 := by nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have h2 : Real.sinh (t / 2)^2 = Real.cosh (t / 2)^2-1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (t / 2)]
  ring_nf at h2
  field_simp [hs, hc]
  ring_nf
  simp only [h1, h2]
  ring

theorem second_abs_le {t : ℝ} (ht : 0 < t) : |second t| ≤ 6 / t ^ 3 := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hc := Real.cosh_pos (t / 2)
  have hs1 := Real.self_le_sinh_iff.mpr ht.le
  have hs3 := cubic_le_sinh ht.le
  have ht3 := pow_pos ht 3
  have hc1 : 1 ≤ Real.cosh (t / 2)^2 := by nlinarith [Real.one_le_cosh (t / 2)]
  have hcp : 0 < Real.cosh (t / 2)^2 := sq_pos_of_pos hc
  have hcc : t ^ 3 ≤ 8 * Real.cosh (t / 2)^2 := by
    have h := one_add_quadratic_le_cosh (by linarith : 0 ≤ t / 2)
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 1+(t / 2)^2/2) h
    nlinarith [sq_nonneg (t*(t - 4))]
  have hf1 : 1 / Real.sinh t ^ 3 ≤ 1 / t ^ 3 := by
    exact one_div_le_one_div_of_le ht3 (pow_le_pow_left₀ ht.le hs1 3)
  have hf2 : 1 / (2 * Real.sinh t) ≤ 3 / t ^ 3 := by
    apply (div_le_div_iff₀ (by positivity) ht3).mpr
    nlinarith
  have hq : 1 / (4 * Real.cosh (t / 2)^2) ≤ 2 / t ^ 3 := by
    apply (div_le_div_iff₀ (by positivity) ht3).mpr
    nlinarith
  have hfac : |1 - 3 / (2 * Real.cosh (t / 2)^2)| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · have h : 3 / (2 * Real.cosh (t / 2)^2) ≤ 2 := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith
      linarith
    · linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 3) (by positivity : 0 ≤ 2*Real.cosh (t / 2)^2)]
  calc
    |second t| ≤ |1 / Real.sinh t ^ 3 + 1 / (2 * Real.sinh t)| +
        |1 / (4 * Real.cosh (t / 2)^2) * (1 - 3 / (2 * Real.cosh (t / 2)^2))| := abs_add_le _ _
    _ ≤ (1 / Real.sinh t ^ 3 + 1 / (2 * Real.sinh t)) + 1 / (4 * Real.cosh (t / 2)^2) := by
      rw [abs_of_nonneg (by positivity), abs_mul, abs_of_nonneg (by positivity)]
      apply add_le_add le_rfl
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac
        (show 0 ≤ 1 / (4 * Real.cosh (t / 2)^2) by positivity)
    _ ≤ 1 / t ^ 3 + 3 / t ^ 3 + 2 / t ^ 3 := add_le_add (add_le_add hf1 hf2) hq
    _ = 6 / t ^ 3 := by ring

theorem contDiffOn_kernel : ContDiffOn ℝ 2 kernel (Ioi 0) := by
  intro t ht
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have hc : Real.cosh (t / 2) ≠ 0 := (Real.cosh_pos _).ne'
  unfold kernel
  have hd1 : ContDiffWithinAt ℝ 2 (fun x : ℝ => 2 * Real.sinh x) (Ioi 0) t := by
    simp only [Real.sinh_eq]; fun_prop
  have hd2 : ContDiffWithinAt ℝ 2 (fun x : ℝ => 4 * Real.cosh (x/2)^2) (Ioi 0) t := by
    simp only [Real.cosh_eq]; fun_prop
  exact (contDiffWithinAt_const.div hd1 (mul_ne_zero (by norm_num) hs)).add
    (contDiffWithinAt_const.div hd2 (mul_ne_zero (by norm_num) (pow_ne_zero _ hc)))

theorem iteratedDeriv_two {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 kernel t = second t := by
  have heq : deriv kernel =ᶠ[nhds t] first := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact (hasDerivAt_kernel hx).deriv
  rw [show (2:ℕ) = 1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [heq.deriv_eq, (hasDerivAt_first ht).deriv]

/-- Exact Taylor remainder, bounded on a half-radius neighborhood. -/
theorem taylor_remainder_le {u h : ℝ} (hu : 0 < u) (hh : |h| ≤ u / 2) :
    |kernel (u + h) - kernel u - h * first u| ≤ 24 * h ^ 2 / u ^ 3 := by
  by_cases hz : h = 0
  · simp [hz]
  have hne : u ≠ u + h := by intro he; apply hz; linarith
  have hlo : u / 2 ≤ min u (u + h) := le_min (by linarith) (by linarith [(abs_le.mp hh).1])
  have hpos (y : ℝ) (hy : y ∈ uIcc u (u + h)) : 0 < y := by
    have hyl : min u (u + h) ≤ y := hy.1
    linarith
  have hcd : ContDiffOn ℝ (↑(1:ℕ)+1) kernel (uIcc u (u + h)) := by
    apply contDiffOn_kernel.mono
    intro y hy
    exact hpos y hy
  obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hcd
  have huy : y ∈ uIcc u (u + h) := ⟨hy.1.le,hy.2.le⟩
  have hud : UniqueDiffWithinAt ℝ (uIcc u (u + h)) u :=
    uniqueDiffOn_Icc (min_lt_max.mpr hne) u (by simp)
  have hwd : derivWithin kernel (uIcc u (u + h)) u = first u :=
    (hasDerivAt_kernel hu).hasDerivWithinAt.derivWithin hud
  have htay : taylorWithinEval kernel 1 (uIcc u (u + h)) u (u + h) =
      kernel u + h * first u := by
    rw [show (1:ℕ) = 0+1 by rfl, taylorWithinEval_succ]
    simp [taylorWithinEval, taylorWithin, taylorCoeffWithin, iteratedDerivWithin_one, hwd]
  rw [htay, iteratedDeriv_two (hpos y huy)] at he
  norm_num at he
  have hylo : u / 2 ≤ y := hlo.trans huy.1
  have hb : |second y| ≤ 48 / u ^ 3 := by
    calc
      _ ≤ 6 / y ^ 3 := second_abs_le (hpos y huy)
      _ ≤ 6 / (u / 2)^3 := div_le_div_of_nonneg_left (by norm_num)
        (by positivity) (pow_le_pow_left₀ (by positivity) hylo 3)
      _ = _ := by field_simp; ring
  have he' : kernel (u + h) - kernel u - h * first u = second y * h ^ 2 / 2 := by
    linarith [he]
  rw [he', abs_div, abs_mul, abs_of_nonneg (sq_nonneg h)]
  norm_num
  calc
    _ ≤ (48 / u ^ 3) * h ^ 2 / 2 := by gcongr
    _ = _ := by ring

def windowMoment (F : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ x in Icc (-1:ℝ) 1, x ^ j * F x

def absoluteSecondMoment (F : ℝ → ℝ) : ℝ :=
  ∫ x in Icc (-1:ℝ) 1, x ^ 2 * |F x|

def windowSample (F : ℝ → ℝ) (T u : ℝ) : ℝ :=
  ∫ x in Icc (-1:ℝ) 1, F x * kernel (u+x / T)

/-- The constant and signed linear moments remain visible in the exact remainder. -/
theorem window_exact_remainder (F : ℝ → ℝ) (hF : Continuous F)
    {T u : ℝ} (hT : 0 < T) (hu : 0 < u) (hscale : 1 / T ≤ u / 2) :
    windowSample F T u - kernel u * windowMoment F 0 -
        (first u / T) * windowMoment F 1 =
      ∫ x in Icc (-1:ℝ) 1,
        F x * (kernel (u+x / T) - kernel u - (x / T)*first u) := by
  have hpos (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) : 0 < u+x / T := by
    have h := div_le_div_of_nonneg_right hx.1 hT.le
    have he : (-1:ℝ)/T = -(1 / T) := by ring
    rw [he] at h
    linarith
  have hk : ContinuousOn (fun x : ℝ => kernel (u+x / T)) (Icc (-1:ℝ) 1) :=
    contDiffOn_kernel.continuousOn.comp (by fun_prop) (fun x hx => hpos x hx)
  have hfi : IntegrableOn F (Icc (-1:ℝ) 1) := hF.continuousOn.integrableOn_Icc
  have hxi : IntegrableOn (fun x => x*F x) (Icc (-1:ℝ) 1) :=
    (continuous_id.mul hF).continuousOn.integrableOn_Icc
  have hki : IntegrableOn (fun x => F x * kernel (u+x / T)) (Icc (-1:ℝ) 1) :=
    (hF.continuousOn.mul hk).integrableOn_Icc
  have he : (∫ x in Icc (-1:ℝ) 1,
      F x * (kernel (u+x / T) - kernel u - (x / T)*first u)) =
      ∫ x in Icc (-1:ℝ) 1,
        (F x * kernel (u+x / T) - kernel u * F x - (first u/T)*(x*F x)) := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [he, integral_sub
    (f := fun x => F x * kernel (u+x / T) - kernel u * F x)
    (g := fun x => (first u/T)*(x*F x))
    (hki.sub (hfi.const_mul (kernel u))) (hxi.const_mul (first u/T)),
    integral_sub (f := fun x => F x * kernel (u+x / T)) (g := fun x => kernel u * F x)
      hki (hfi.const_mul (kernel u)), integral_const_mul, integral_const_mul]
  simp [windowSample, windowMoment]

/-- An unconditional second-moment estimate for the explicit spatial kernel. -/
theorem window_remainder_bound (F : ℝ → ℝ) (hF : Continuous F)
    {T u : ℝ} (hT : 0 < T) (hu : 0 < u) (hscale : 1 / T ≤ u / 2) :
    |windowSample F T u - kernel u * windowMoment F 0 -
        (first u / T) * windowMoment F 1| ≤
      24 * absoluteSecondMoment F / (T ^ 2 * u ^ 3) := by
  rw [window_exact_remainder F hF hT hu hscale]
  have hm : IntegrableOn (fun x : ℝ => (24/(T ^ 2*u ^ 3))*(x ^ 2*|F x|)) (Icc (-1:ℝ) 1) :=
    (by fun_prop : Continuous (fun x : ℝ =>
      (24/(T ^ 2*u ^ 3))*(x ^ 2*|F x|))).continuousOn.integrableOn_Icc
  have h := norm_integral_le_of_norm_le hm
    (g := fun x : ℝ => (24/(T ^ 2*u ^ 3))*(x ^ 2*|F x|)) (f := fun x : ℝ =>
      F x * (kernel (u+x / T) - kernel u - (x / T)*first u)) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hh : |x / T| ≤ u / 2 := by
      rw [abs_div, abs_of_pos hT]
      exact (div_le_div_of_nonneg_right (abs_le.mpr hx) hT.le).trans hscale
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |F x| * (24*(x / T)^2/u ^ 3) :=
        mul_le_mul_of_nonneg_left (taylor_remainder_le hu hh) (abs_nonneg _)
      _ = _ := by field_simp)
  rw [Real.norm_eq_abs, integral_const_mul] at h
  simpa [absoluteSecondMoment, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- Both ordinary moments are discharged by the test, not assumed of the zeros. -/
theorem window_bound_of_two_moments (F : ℝ → ℝ) (hF : Continuous F)
    (h0 : windowMoment F 0 = 0) (h1 : windowMoment F 1 = 0)
    {T u : ℝ} (hT : 0 < T) (hu : 0 < u) (hscale : 1 / T ≤ u / 2) :
    |windowSample F T u| ≤ 24 * absoluteSecondMoment F / (T ^ 2 * u ^ 3) := by
  simpa [h0, h1] using window_remainder_bound F hF hT hu hscale

/-- The normalization contributes the third inverse power of the height. -/
theorem normalized_window_bound (F : ℝ → ℝ) (hF : Continuous F)
    (h0 : windowMoment F 0 = 0) (h1 : windowMoment F 1 = 0)
    {T u : ℝ} (hT : 1 < T) (hu : 0 < u) (hscale : 1 / T ≤ u / 2) :
    |-(windowSample F T u) / (T * Real.log T)| ≤
      24 * absoluteSecondMoment F / (T ^ 3 * Real.log T * u ^ 3) := by
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  rw [abs_div, abs_neg, abs_of_pos (mul_pos hT0 hlog)]
  calc
    _ ≤ (24 * absoluteSecondMoment F / (T ^ 2 * u ^ 3)) / (T * Real.log T) :=
      div_le_div_of_nonneg_right (window_bound_of_two_moments F hF h0 h1 hT0 hu hscale)
        (mul_pos hT0 hlog).le
    _ = _ := by ring

theorem first_moment_eq_zero_of_even (F : ℝ → ℝ) (hFe : ∀ x, F (-x) = F x) :
    windowMoment F 1 = 0 := by
  let g : ℝ → ℝ := (Icc (-1:ℝ) 1).indicator (fun x => x*F x)
  have hg : ∀ x, g (-x) = -g x := by
    intro x
    have hm : (-x ∈ Icc (-1:ℝ) 1) ↔ (x ∈ Icc (-1:ℝ) 1) := by
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    simp only [g, indicator_apply, hm, hFe]
    split_ifs <;> ring
  letI : (volume : Measure ℝ).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular volume
  have h := integral_neg_eq_self g volume
  simp_rw [hg] at h
  rw [integral_neg] at h
  have hz : (∫ x : ℝ, g x) = 0 := by linarith
  simpa [g, integral_indicator measurableSet_Icc, windowMoment] using hz

theorem normalized_window_bound_of_even (F : ℝ → ℝ) (hF : Continuous F)
    (hFe : ∀ x, F (-x) = F x) (h0 : windowMoment F 0 = 0)
    {T u : ℝ} (hT : 1 < T) (hu : 0 < u) (hscale : 1 / T ≤ u / 2) :
    |-(windowSample F T u) / (T * Real.log T)| ≤
      24 * absoluteSecondMoment F / (T ^ 3 * Real.log T * u ^ 3) :=
  normalized_window_bound F hF h0 (first_moment_eq_zero_of_even F hFe) hT hu hscale

end RiemannResearch.Analysis.SechGammaBounds
