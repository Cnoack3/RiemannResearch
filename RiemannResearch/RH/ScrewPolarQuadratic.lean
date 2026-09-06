/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticScrewKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact polar quadratic form

The polar summand of the elementary arithmetic screw function is evaluated as
an exact rank-two quadratic form. For an integrable real test with integrable
positive and negative exponential moments, the iterated integral is the
product of those moments plus the constant-kernel correction. On mean-zero
tests the correction vanishes. The hyperbolic rewrite retains the negative
cosh square and positive sinh square. Both versions specialize to the
project's dyadic Haar steps.

Source: the signed decomposition in the user-provided
RH_Local_to_Global_Trace_Attack_Plan_2026-09-05.pdf supports the statement and
its exponential factorization. This module proves only the polar component.
It does not prove positivity of the complete arithmetic kernel, density, a
Weil-form identification, or RH.
-/

namespace RiemannResearch.RH
open MeasureTheory
open RiemannResearch.Analysis
open RiemannResearch.RH.PrimeGapCurvature
noncomputable section

private theorem screwPolarPart_inner_integral
    (u : ℝ → ℝ)
    (hu : Integrable u)
    (hp : Integrable (fun x => u x * Real.exp (x / 2)))
    (hm : Integrable (fun x => u x * Real.exp (-x / 2)))
    (x : ℝ) :
    (∫ y, screwPolarPart (x - y) * u y) =
      -4 * (Real.exp (x / 2) * (∫ y, Real.exp (-y / 2) * u y) +
        Real.exp (-x / 2) * (∫ y, Real.exp (y / 2) * u y) -
        2 * (∫ y, u y)) := by
  have hp' : Integrable (fun y => Real.exp (y / 2) * u y) := by
    simpa only [mul_comm] using hp
  have hm' : Integrable (fun y => Real.exp (-y / 2) * u y) := by
    simpa only [mul_comm] using hm
  have he1 (y : ℝ) :
      Real.exp ((x - y) / 2) =
        Real.exp (x / 2) * Real.exp (-y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 (y : ℝ) :
      Real.exp (-(x - y) / 2) =
        Real.exp (-x / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  let f : ℝ → ℝ :=
    fun y => Real.exp (x / 2) * (Real.exp (-y / 2) * u y)
  let g : ℝ → ℝ :=
    fun y => Real.exp (-x / 2) * (Real.exp (y / 2) * u y)
  let h : ℝ → ℝ := fun y => 2 * u y
  have hf : Integrable f := hm'.const_mul _
  have hg : Integrable g := hp'.const_mul _
  have hh : Integrable h := hu.const_mul 2
  have hpoint (y : ℝ) :
      screwPolarPart (x - y) * u y = -4 * ((f + g - h) y) := by
    change screwPolarPart (x - y) * u y = -4 * (f y + g y - h y)
    unfold screwPolarPart f g h
    rw [he1 y, he2 y]
    ring
  calc
    (∫ y, screwPolarPart (x - y) * u y) =
        ∫ y, -4 * ((f + g - h) y) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = -4 * (∫ y, (f + g - h) y) :=
      integral_const_mul (-4) (f + g - h)
    _ = -4 * ((∫ y, (f + g) y) - ∫ y, h y) :=
      congrArg (fun q : ℝ => -4 * q) (integral_sub (hf.add hg) hh)
    _ = -4 * (((∫ y, f y) + ∫ y, g y) - ∫ y, h y) :=
      congrArg (fun q : ℝ => -4 * (q - ∫ y, h y))
        (integral_add hf hg)
    _ = _ := by
      unfold f g h
      rw [integral_const_mul, integral_const_mul, integral_const_mul]

/-- Exact polar quadratic identity, including the constant-kernel correction. -/
theorem screwPolarPart_quadratic_integral
    (u : ℝ → ℝ)
    (hu : Integrable u)
    (hp : Integrable (fun x => u x * Real.exp (x / 2)))
    (hm : Integrable (fun x => u x * Real.exp (-x / 2))) :
    (∫ x, u x * (∫ y, screwPolarPart (x - y) * u y)) =
      -8 * (∫ x, u x * Real.exp (x / 2)) *
        (∫ x, u x * Real.exp (-x / 2)) +
      8 * (∫ x, u x) ^ 2 := by
  have hp_comm :
      (∫ x, Real.exp (x / 2) * u x) =
        ∫ x, u x * Real.exp (x / 2) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hm_comm :
      (∫ x, Real.exp (-x / 2) * u x) =
        ∫ x, u x * Real.exp (-x / 2) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  simp_rw [screwPolarPart_inner_integral u hu hp hm]
  let p : ℝ → ℝ :=
    fun x => (u x * Real.exp (x / 2)) *
      (∫ y, Real.exp (-y / 2) * u y)
  let m : ℝ → ℝ :=
    fun x => (u x * Real.exp (-x / 2)) *
      (∫ y, Real.exp (y / 2) * u y)
  let z : ℝ → ℝ := fun x => 2 * u x * (∫ y, u y)
  have hpInt : Integrable p := hp.mul_const _
  have hmInt : Integrable m := hm.mul_const _
  have hzInt : Integrable z := by
    unfold z
    fun_prop
  have hpoint (x : ℝ) :
      u x * (-4 * (Real.exp (x / 2) *
          (∫ y, Real.exp (-y / 2) * u y) +
        Real.exp (-x / 2) * (∫ y, Real.exp (y / 2) * u y) -
        2 * (∫ y, u y))) =
        -4 * ((p + m - z) x) := by
    change _ = -4 * (p x + m x - z x)
    unfold p m z
    ring
  calc
    (∫ x, u x * (-4 * (Real.exp (x / 2) *
        (∫ y, Real.exp (-y / 2) * u y) +
        Real.exp (-x / 2) * (∫ y, Real.exp (y / 2) * u y) -
        2 * (∫ y, u y)))) =
      ∫ x, -4 * ((p + m - z) x) :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = -4 * (∫ x, (p + m - z) x) :=
      integral_const_mul (-4) (p + m - z)
    _ = -4 * ((∫ x, (p + m) x) - ∫ x, z x) :=
      congrArg (fun q : ℝ => -4 * q)
        (integral_sub (hpInt.add hmInt) hzInt)
    _ = -4 * (((∫ x, p x) + ∫ x, m x) - ∫ x, z x) :=
      congrArg (fun q : ℝ => -4 * (q - ∫ x, z x))
        (integral_add hpInt hmInt)
    _ = _ := by
      unfold p m z
      rw [integral_mul_const, integral_mul_const, integral_mul_const,
        integral_const_mul, hp_comm, hm_comm]
      ring

/-- On a mean-zero test, the polar quadratic form is the signed rank-two
exponential-moment product. -/
theorem screwPolarPart_quadratic_integral_of_zero
    (u : ℝ → ℝ)
    (hu : Integrable u)
    (hp : Integrable (fun x => u x * Real.exp (x / 2)))
    (hm : Integrable (fun x => u x * Real.exp (-x / 2)))
    (hzero : (∫ x, u x) = 0) :
    (∫ x, u x * (∫ y, screwPolarPart (x - y) * u y)) =
      -8 * (∫ x, u x * Real.exp (x / 2)) *
        (∫ x, u x * Real.exp (-x / 2)) := by
  rw [screwPolarPart_quadratic_integral u hu hp hm, hzero]
  ring

/-- Exact polar contribution for every dyadic Haar step. No sign is asserted
for the product of its two exponential moments. -/
theorem dyadicHaarStep_screwPolarPart_quadratic
    {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, screwPolarPart (x - y) * dyadicHaarStep R m c y)) =
      -8 * (∫ x, dyadicHaarStep R m c x * Real.exp (x / 2)) *
        (∫ x, dyadicHaarStep R m c x * Real.exp (-x / 2)) := by
  apply screwPolarPart_quadratic_integral_of_zero
      (u := dyadicHaarStep R m c)
  · simpa only [mul_one] using
      integrable_dyadicHaarStep_mul_continuous
        R m c (fun _ => (1 : ℝ)) continuous_const
  · exact integrable_dyadicHaarStep_mul_continuous R m c
      (fun x => Real.exp (x / 2))
      (Real.continuous_exp.comp (continuous_id.div_const 2))
  · exact integrable_dyadicHaarStep_mul_continuous R m c
      (fun x => Real.exp (-x / 2))
      (Real.continuous_exp.comp (continuous_neg.div_const 2))
  · exact dyadicHaarStep_integral_zero hR m c

/-- Exact hyperbolic polar identity; the mean correction is retained. -/
theorem screwPolarPart_quadratic_integral_hyperbolic
    (u : ℝ → ℝ)
    (hu : Integrable u)
    (hp : Integrable (fun x => u x * Real.exp (x / 2)))
    (hm : Integrable (fun x => u x * Real.exp (-x / 2))) :
    (∫ x, u x * (∫ y, screwPolarPart (x - y) * u y)) =
      -8 * (∫ x, u x * Real.cosh (x / 2)) ^ 2 +
      8 * (∫ x, u x * Real.sinh (x / 2)) ^ 2 +
      8 * (∫ x, u x) ^ 2 := by
  have hC :
      (∫ x, u x * Real.cosh (x / 2)) =
        ((∫ x, u x * Real.exp (x / 2)) +
          (∫ x, u x * Real.exp (-x / 2))) / 2 := by
    calc
      (∫ x, u x * Real.cosh (x / 2)) =
          ∫ x, (u x * Real.exp (x / 2) +
            u x * Real.exp (-x / 2)) / 2 := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.cosh_eq]
        simp only [neg_div]
        ring
      _ = _ := by rw [integral_div, integral_add hp hm]
  have hS :
      (∫ x, u x * Real.sinh (x / 2)) =
        ((∫ x, u x * Real.exp (x / 2)) -
          (∫ x, u x * Real.exp (-x / 2))) / 2 := by
    calc
      (∫ x, u x * Real.sinh (x / 2)) =
          ∫ x, (u x * Real.exp (x / 2) -
            u x * Real.exp (-x / 2)) / 2 := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.sinh_eq]
        simp only [neg_div]
        ring
      _ = _ := by rw [integral_div, integral_sub hp hm]
  rw [screwPolarPart_quadratic_integral u hu hp hm, hC, hS]
  ring

/-- On mean-zero tests the polar form has a negative cosh and positive sinh square. -/
theorem screwPolarPart_quadratic_integral_hyperbolic_of_zero
    (u : ℝ → ℝ)
    (hu : Integrable u)
    (hp : Integrable (fun x => u x * Real.exp (x / 2)))
    (hm : Integrable (fun x => u x * Real.exp (-x / 2)))
    (hzero : (∫ x, u x) = 0) :
    (∫ x, u x * (∫ y, screwPolarPart (x - y) * u y)) =
      -8 * (∫ x, u x * Real.cosh (x / 2)) ^ 2 +
      8 * (∫ x, u x * Real.sinh (x / 2)) ^ 2 := by
  rw [screwPolarPart_quadratic_integral_hyperbolic u hu hp hm, hzero]
  ring

/-- Exact signed hyperbolic polar form on dyadic Haar steps. -/
theorem dyadicHaarStep_screwPolarPart_quadratic_hyperbolic
    {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, screwPolarPart (x - y) * dyadicHaarStep R m c y)) =
      -8 * (∫ x, dyadicHaarStep R m c x * Real.cosh (x / 2)) ^ 2 +
      8 * (∫ x, dyadicHaarStep R m c x * Real.sinh (x / 2)) ^ 2 := by
  apply screwPolarPart_quadratic_integral_hyperbolic_of_zero
      (u := dyadicHaarStep R m c)
  · simpa only [mul_one] using
      integrable_dyadicHaarStep_mul_continuous
        R m c (fun _ => (1 : ℝ)) continuous_const
  · exact integrable_dyadicHaarStep_mul_continuous R m c
      (fun x => Real.exp (x / 2))
      (Real.continuous_exp.comp (continuous_id.div_const 2))
  · exact integrable_dyadicHaarStep_mul_continuous R m c
      (fun x => Real.exp (-x / 2))
      (Real.continuous_exp.comp (continuous_neg.div_const 2))
  · exact dyadicHaarStep_integral_zero hR m c


end
end RiemannResearch.RH
