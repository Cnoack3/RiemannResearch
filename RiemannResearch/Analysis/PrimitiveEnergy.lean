/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Primitive energy for the absolute-value kernel

The signed absolute-value quadratic form of a compactly supported integrable
real mean-zero test is minus twice the square integral of its cumulative
primitive. The proof first establishes absolute integrability of the
three-variable cut integrand, then applies Fubini. The cut identity uses
literal Ico endpoints; no endpoint convention for finite cells is changed.

Source: user-provided RH_Local_to_Global_Trace_Attack_Plan_2026-09-05,
page 2, supplies the identity; the canonical handoff v34 supplies the
cut-indicator/Fubini proof strategy. RH consumer: the linear component of
the signed arithmetic screw decomposition. This is component nonpositivity,
not positivity of the complete Weil form or an RH proof.
-/

open MeasureTheory Set
namespace RiemannResearch.Analysis
noncomputable section
def cumulativeCut (x t : ℝ) : ℝ := if x ≤ t then 1 else 0
@[fun_prop] theorem measurable_cumulativeCut :
    Measurable (Function.uncurry cumulativeCut) := by
  change Measurable (fun p : ℝ × ℝ => if p.1 ≤ p.2 then (1 : ℝ) else 0)
  exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
    measurable_const measurable_const
theorem cumulativeCut_sub_sq (x y t : ℝ) :
    (cumulativeCut x t - cumulativeCut y t)^2 =
      (Ico (min x y) (max x y)).indicator (fun _ => (1 : ℝ)) t := by
  rcases le_total x y with hxy | hyx
  · by_cases hx : x ≤ t <;> by_cases hy : y ≤ t <;>
      simp [cumulativeCut, min_eq_left hxy, max_eq_right hxy,
        mem_Ico, ← not_le, hx, hy]; linarith
  · by_cases hx : x ≤ t <;> by_cases hy : y ≤ t <;>
      simp [cumulativeCut, min_eq_right hyx, max_eq_left hyx,
        mem_Ico, ← not_le, hx, hy]; linarith
theorem norm_cumulativeCut_sub_sq_le (x y t : ℝ) :
    ‖(cumulativeCut x t - cumulativeCut y t)^2‖ ≤ 1 := by
  by_cases hx : x ≤ t <;> by_cases hy : y ≤ t <;> norm_num [cumulativeCut, hx, hy]
theorem integral_cumulativeCut_sub_sq {a b x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (∫ t in Icc a b, (cumulativeCut x t - cumulativeCut y t)^2) = |x-y| := by
  simp_rw [cumulativeCut_sub_sq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Ico, integral_const,
      measureReal_restrict_apply_univ]
    simp only [Measure.real, Real.volume_Ico, smul_eq_mul, mul_one,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max))]
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
  · intro t ht
    apply indicator_of_notMem
    intro h
    apply ht
    exact ⟨(le_min hx.1 hy.1).trans h.1, h.2.le.trans (max_le hx.2 hy.2)⟩
theorem integrable_cumulativeCut_triple (a b : ℝ) (u : ℝ → ℝ)
    (hu : Integrable u) :
    Integrable (fun p : (ℝ × ℝ) × ℝ =>
      (u p.1.1 * u p.1.2) * (cumulativeCut p.1.1 p.2 - cumulativeCut p.1.2 p.2)^2)
      ((volume.prod volume).prod (volume.restrict (Icc a b))) := by
  have hbase : Integrable (fun p : (ℝ × ℝ) × ℝ => u p.1.1 * u p.1.2)
      ((volume.prod volume).prod (volume.restrict (Icc a b))) := by
    simpa only [mul_one] using
      (hu.mul_prod hu).mul_prod (integrable_const (1 : ℝ) :
        Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc a b)))
  apply hbase.mul_bdd
  · have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
        (cumulativeCut p.1.1 p.2 - cumulativeCut p.1.2 p.2)^2) := by fun_prop
    exact hm.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun p =>
      norm_cumulativeCut_sub_sq_le p.1.1 p.1.2 p.2)
theorem cumulativeCut_cross (u : ℝ → ℝ) (x y t : ℝ) :
    (u x * u y) * (cumulativeCut x t - cumulativeCut y t)^2 =
      (u x * cumulativeCut x t) * (u y * (1 - cumulativeCut y t)) +
      (u x * (1 - cumulativeCut x t)) * (u y * cumulativeCut y t) := by
  by_cases hx : x ≤ t <;> by_cases hy : y ≤ t <;> simp [cumulativeCut, hx, hy]
theorem integrable_mul_cumulativeCut (u : ℝ → ℝ) (hu : Integrable u) (t : ℝ) :
    Integrable (fun x => u x * cumulativeCut x t) := by
  have he : (fun x => u x * cumulativeCut x t) = (Iic t).indicator u := by
    funext x
    by_cases hx : x ≤ t <;> simp [cumulativeCut, hx]
  rw [he]
  exact hu.indicator measurableSet_Iic
theorem integral_mul_cumulativeCut (u : ℝ → ℝ) (t : ℝ) :
    (∫ x, u x * cumulativeCut x t) = ∫ x in Iic t, u x := by
  have he : (fun x => u x * cumulativeCut x t) = (Iic t).indicator u := by
    funext x
    by_cases hx : x ≤ t <;> simp [cumulativeCut, hx]
  rw [he, integral_indicator measurableSet_Iic]
theorem integral_cumulativeCut_cross (u : ℝ → ℝ) (hu : Integrable u) (t : ℝ) :
    (∫ xy : ℝ × ℝ, (u xy.1 * u xy.2) *
      (cumulativeCut xy.1 t - cumulativeCut xy.2 t)^2) =
      2 * (∫ x in Iic t, u x) * ((∫ x, u x) - (∫ x in Iic t, u x)) := by
  have hcut := integrable_mul_cumulativeCut u hu t
  have hcomp : Integrable (fun x => u x * (1 - cumulativeCut x t)) := by
    convert hu.sub hcut using 1
    ext x
    simp only [Pi.sub_apply, mul_sub, mul_one]
  rw [Measure.volume_eq_prod ℝ ℝ]
  simp_rw [cumulativeCut_cross]
  rw [integral_add (hcut.mul_prod hcomp) (hcomp.mul_prod hcut),
    integral_prod_mul (fun x => u x * cumulativeCut x t)
      (fun x => u x * (1 - cumulativeCut x t)),
    integral_prod_mul (fun x => u x * (1 - cumulativeCut x t))
      (fun x => u x * cumulativeCut x t)]
  have hc : (∫ x, u x * (1 - cumulativeCut x t)) =
      (∫ x, u x) - (∫ x in Iic t, u x) := by
    simp_rw [mul_sub, mul_one]
    rw [integral_sub hu hcut, integral_mul_cumulativeCut]
  rw [hc, integral_mul_cumulativeCut]
  ring
theorem absKernel_integral_cumulative (a b : ℝ) (u : ℝ → ℝ)
    (hu : Integrable u) (hsupport : ∀ x ∉ Icc a b, u x = 0) :
    (∫ x, u x * (∫ y, |x-y| * u y)) =
      ∫ t in Icc a b, 2 * (∫ x in Iic t, u x) *
        ((∫ x, u x) - (∫ x in Iic t, u x)) := by
  let F : (ℝ × ℝ) × ℝ → ℝ := fun p =>
    (u p.1.1 * u p.1.2) * (cumulativeCut p.1.1 p.2 - cumulativeCut p.1.2 p.2)^2
  let K : ℝ × ℝ → ℝ := fun p => u p.1 * |p.1-p.2| * u p.2
  have hF : Integrable F ((volume.prod volume).prod (volume.restrict (Icc a b))) :=
    integrable_cumulativeCut_triple a b u hu
  have hz (xy : ℝ × ℝ) : (∫ t in Icc a b, F (xy,t)) = K xy := by
    by_cases hx : xy.1 ∈ Icc a b
    · by_cases hy : xy.2 ∈ Icc a b
      · change (∫ t in Icc a b, (u xy.1 * u xy.2) *
          (cumulativeCut xy.1 t - cumulativeCut xy.2 t)^2) = _
        rw [integral_const_mul, integral_cumulativeCut_sub_sq hx hy]
        dsimp [K]
        ring
      · simp [F, K, hsupport xy.2 hy]
    · simp [F, K, hsupport xy.1 hx]
  have hK : Integrable K (volume.prod volume) := by
    have h := hF.integral_prod_left
    simpa only [hz] using h
  have hinner (x : ℝ) : (∫ y, K (x,y)) =
      u x * (∫ y, |x-y| * u y) := by
    simpa only [K, mul_assoc] using
      integral_const_mul (μ := volume) (u x) (fun y => |x-y| * u y)
  calc
    (∫ x, u x * (∫ y, |x-y| * u y)) =
        ∫ xy, K xy ∂volume.prod volume := by
      rw [integral_prod K hK]
      simp_rw [hinner]
    _ = ∫ xy, (∫ t in Icc a b, F (xy,t)) ∂volume.prod volume := by
      simp_rw [hz]
    _ = ∫ t in Icc a b, ∫ xy, F (xy,t) ∂volume.prod volume :=
      (integral_prod F hF).symm.trans (integral_prod_symm F hF)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      simpa only [F, ← Measure.volume_eq_prod] using integral_cumulativeCut_cross u hu t

theorem cumulativeIntegral_eq_zero_of_not_mem (a b : ℝ) (u : ℝ → ℝ)
    (hsupport : ∀ x ∉ Icc a b, u x = 0) (hmean : (∫ x, u x) = 0)
    {t : ℝ} (ht : t ∉ Icc a b) : (∫ x in Iic t, u x) = 0 := by
  rcases not_and_or.mp ht with hleft | hright
  · apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply hsupport x
    intro h
    exact hleft (h.1.trans hx)
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hmean]
    intro x hx
    apply hsupport x
    intro h
    exact hx (h.2.trans (le_of_not_ge hright))

theorem absKernel_integral_eq_neg_two_cumulative_sq (a b : ℝ) (u : ℝ → ℝ)
    (hu : Integrable u) (hsupport : ∀ x ∉ Icc a b, u x = 0)
    (hmean : (∫ x, u x) = 0) :
    (∫ x, u x * (∫ y, |x-y| * u y)) =
      -2 * (∫ t, (∫ x in Iic t, u x)^2) := by
  rw [absKernel_integral_cumulative a b u hu hsupport]
  have he (t : ℝ) : 2 * (∫ x in Iic t, u x) *
      ((∫ x, u x) - (∫ x in Iic t, u x)) =
      -2 * (∫ x in Iic t, u x)^2 := by rw [hmean]; ring
  simp_rw [he]
  rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro t ht
  rw [cumulativeIntegral_eq_zero_of_not_mem a b u hsupport hmean ht, zero_pow (by decide)]
theorem integrable_cumulativeIntegral_sq (a b : ℝ) (u : ℝ → ℝ)
    (hu : Integrable u) (hsupport : ∀ x ∉ Icc a b, u x = 0)
    (hmean : (∫ x, u x) = 0) :
    Integrable (fun t => (∫ x in Iic t, u x)^2) := by
  have hF := integrable_cumulativeCut_triple a b u hu
  have hi := hF.integral_prod_right
  have he (t : ℝ) : (∫ xy : ℝ × ℝ,
      (u xy.1 * u xy.2) *
        (cumulativeCut xy.1 t - cumulativeCut xy.2 t)^2 ∂volume.prod volume) =
      -2 * (∫ x in Iic t, u x)^2 := by
    rw [← Measure.volume_eq_prod ℝ ℝ, integral_cumulativeCut_cross u hu t, hmean]
    ring
  simp_rw [he] at hi
  have hs : IntegrableOn (fun t => (∫ x in Iic t, u x)^2) (Icc a b) := by
    change Integrable (fun t => (∫ x in Iic t, u x)^2) (volume.restrict (Icc a b))
    convert hi.const_mul (-1/2 : ℝ) using 1
    ext t
    ring
  have hind := hs.integrable_indicator measurableSet_Icc
  apply hind.congr
  filter_upwards with t
  by_cases ht : t ∈ Icc a b
  · simp [ht]
  · simp [ht, cumulativeIntegral_eq_zero_of_not_mem a b u hsupport hmean ht]

theorem absKernel_integral_nonpos (a b : ℝ) (u : ℝ → ℝ)
    (hu : Integrable u) (hsupport : ∀ x ∉ Icc a b, u x = 0)
    (hmean : (∫ x, u x) = 0) :
    (∫ x, u x * (∫ y, |x-y| * u y)) ≤ 0 := by
  rw [absKernel_integral_eq_neg_two_cumulative_sq a b u hu hsupport hmean]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (integral_nonneg (fun t => sq_nonneg _))
end
end RiemannResearch.Analysis
