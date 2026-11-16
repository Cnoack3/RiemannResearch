/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Horizontal contour shifts from a Gaussian majorant

A uniform Gaussian bound on a closed horizontal strip supplies absolute
convergence on every horizontal line and vanishing of both vertical sides.
The finite Cauchy rectangle retains its orientations before passage to the limit.
Concrete consumer: logarithmic-coordinate ray rotation for the Gaussian
arithmetic transform. Source: user-provided logarithmic-coordinate argument,
using Mathlib's Cauchy--Goursat theorem on rectangles.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
namespace Complex

theorem integrable_horizontal_of_gaussian_bound {f : ℂ → ℂ} {a b C q y : ℝ}
    (hq : 0 < q)
    (hd : ∀ z : ℂ, z.im ∈ uIcc a b → DifferentiableAt ℂ f z)
    (hbound : ∀ x : ℝ, ∀ y ∈ uIcc a b,
      ‖f ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-q * x^2))
    (hy : y ∈ uIcc a b) :
    Integrable (fun x : ℝ => f ((x : ℂ) + y * I)) := by
  have hc : Continuous (fun x : ℝ => f ((x : ℂ) + y * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (hd _ (by simpa using hy)).continuousAt.comp
    exact Complex.continuous_ofReal.continuousAt.add continuousAt_const
  exact ((integrable_exp_neg_mul_sq hq).const_mul C).mono'
    hc.aestronglyMeasurable (Eventually.of_forall fun x => hbound x y hy)

/-- A proved Gaussian majorant discharges both convergence and all rectangle tails. -/
theorem integral_horizontal_eq_of_gaussian_bound {f : ℂ → ℂ} {a b C q : ℝ}
    (hq : 0 < q)
    (hd : ∀ z : ℂ, z.im ∈ uIcc a b → DifferentiableAt ℂ f z)
    (hbound : ∀ x : ℝ, ∀ y ∈ uIcc a b,
      ‖f ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-q * x^2)) :
    (∫ x : ℝ, f ((x : ℂ) + a * I)) =
      ∫ x : ℝ, f ((x : ℂ) + b * I) := by
  let V (x : ℝ) := ∫ y in a..b, f ((x : ℂ) + y * I)
  have hV (x : ℝ) : ‖V x‖ ≤ C * Real.exp (-q * x^2) * |b-a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y hy => hbound x y (uIoc_subset_uIcc hy))
  have hexp : Tendsto (fun x : ℝ => Real.exp (-q * x^2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hp : Tendsto (fun x : ℝ => x^2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    exact hp.const_mul_atTop_of_neg (neg_neg_of_pos hq)
  have hlim : Tendsto (fun x : ℝ => C * Real.exp (-q*x^2) * |b-a|) atTop (𝓝 0) := by
    simpa using (hexp.const_mul C).mul_const |b-a|
  have hpos : Tendsto V atTop (𝓝 0) := squeeze_zero_norm hV hlim
  have hneg : Tendsto (fun x => V (-x)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun x => by simpa only [neg_sq] using hV (-x)) hlim
  have ha := intervalIntegral_tendsto_integral
    (integrable_horizontal_of_gaussian_bound hq hd hbound (left_mem_uIcc))
    tendsto_neg_atTop_atBot tendsto_id
  have hb := intervalIntegral_tendsto_integral
    (integrable_horizontal_of_gaussian_bound hq hd hbound (right_mem_uIcc))
    tendsto_neg_atTop_atBot tendsto_id
  have hrect (T : ℝ) :
      (∫ x in -T..T, f ((x : ℂ) + a * I)) -
        (∫ x in -T..T, f ((x : ℂ) + b * I)) + I * V T - I * V (-T) = 0 := by
    have hh := integral_boundary_rect_eq_zero_of_differentiableOn f
      (((-T : ℝ) : ℂ) + a * I) ((T : ℂ) + b * I) (by
        intro z hz
        apply (hd z ?_).differentiableWithinAt
        simpa using (mem_reProdIm.mp hz).2)
    simpa [V, smul_eq_mul] using hh
  have hlimrect := ((ha.sub hb).add (hpos.const_mul I)).sub (hneg.const_mul I)
  have heq := tendsto_nhds_unique hlimrect
    (tendsto_const_nhds.congr' (Eventually.of_forall fun T => (hrect T).symm))
  simpa using sub_eq_zero.mp (by simpa using heq :
    (∫ x : ℝ, f ((x : ℂ) + a * I)) - (∫ x : ℝ, f ((x : ℂ) + b * I)) = 0)

end Complex
