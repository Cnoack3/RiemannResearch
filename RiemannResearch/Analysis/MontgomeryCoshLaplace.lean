/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryPoisson
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Exact Laplace energy of the horizontal cosh defect

Source: the actual-zero cosh correction in the user Montgomery continuation
handoff, route B; the existing bilateral transform is the analytic provider.
We evaluate the complete scalar energy, including its negative middle term.
This is a convergent integral identity on |d|<1, not a zero-density input.
-/

noncomputable section
open MeasureTheory

namespace RiemannResearch.Analysis.MontgomeryCoshLaplace
open MontgomeryPoisson

def realFeature (d s : ℝ) : ℝ := Real.exp (-2 * |s| + s*d)

theorem feature_real (d s : ℝ) :
    feature 2 (d : ℂ) s = (realFeature d s : ℂ) := by
  unfold feature realFeature
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem integrable_realFeature (d : ℝ) (hd : |d| < 2) :
    Integrable (realFeature d) := by
  have h := (integrable_feature 2 (d : ℂ) (by simpa using hd)).re
  change Integrable (fun s : ℝ => (feature 2 (d : ℂ) s).re) at h
  simpa only [feature_real, Complex.ofReal_re] using h

theorem integral_realFeature (d : ℝ) (hd : |d| < 2) :
    (∫ s : ℝ, realFeature d s) = 4 / (4-d^2) := by
  have h := integral_re (integrable_feature 2 (d : ℂ) (by simpa using hd))
  change (∫ s : ℝ, (feature 2 (d : ℂ) s).re) =
    (∫ s : ℝ, feature 2 (d : ℂ) s).re at h
  rw [integral_feature 2 (d : ℂ) (by simpa using hd)] at h
  have he : 2*((2 : ℝ) : ℂ)/(((2 : ℝ) : ℂ)^2-(d : ℂ)^2) =
      ((4/(4-d^2) : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [feature_real, he, Complex.ofReal_re] using h

def coshFeature (u d s : ℝ) : ℝ :=
  Real.exp (-2*|s|) * Real.cosh ((u+s)*d)

theorem coshFeature_expansion (u d s : ℝ) :
    coshFeature u d s =
      (Real.exp (u*d)/2) * realFeature d s +
      (Real.exp (-(u*d))/2) * realFeature (-d) s := by
  unfold coshFeature realFeature
  rw [Real.cosh_eq]
  have hp : Real.exp (-2*|s|) * Real.exp ((u+s)*d) =
      Real.exp (u*d) * Real.exp (-2*|s|+s*d) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp (-2*|s|) * Real.exp (-((u+s)*d)) =
      Real.exp (-(u*d)) * Real.exp (-2*|s|+s*(-d)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-2*|s|) * Real.exp ((u+s)*d) +
        Real.exp (-2*|s|) * Real.exp (-((u+s)*d)))/2 := by ring
    _ = _ := by rw [hp, hm]; ring

theorem integrable_coshFeature (u d : ℝ) (hd : |d| < 2) :
    Integrable (coshFeature u d) := by
  change Integrable (fun s : ℝ => coshFeature u d s)
  simp_rw [coshFeature_expansion]
  exact ((integrable_realFeature d hd).const_mul _).add
    ((integrable_realFeature (-d) (by simpa using hd)).const_mul _)

theorem integral_coshFeature (u d : ℝ) (hd : |d| < 2) :
    (∫ s : ℝ, coshFeature u d s) = 4*Real.cosh (u*d)/(4-d^2) := by
  simp_rw [coshFeature_expansion]
  rw [integral_add ((integrable_realFeature d hd).const_mul _)
    ((integrable_realFeature (-d) (by simpa using hd)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_realFeature d hd, integral_realFeature (-d) (by simpa using hd)]
  rw [Real.cosh_eq]
  ring

def defectFeature (u d s : ℝ) : ℝ :=
  Real.exp (-2*|s|) * (Real.cosh ((u+s)*d)-1)^2

def diagonalEnergy (u d : ℝ) : ℝ :=
  Real.cosh (2*u*d)/(2*(1-d^2)) -
    8*Real.cosh (u*d)/(4-d^2) + 3/2

theorem defectFeature_expansion (u d s : ℝ) :
    defectFeature u d s =
      (1/2)*coshFeature u (2*d) s - 2*coshFeature u d s +
        (3/2)*coshFeature u 0 s := by
  unfold defectFeature coshFeature
  have h (x : ℝ) : Real.cosh (2*x) = 2 * Real.cosh x ^ 2 - 1 := by
    rw [Real.cosh_eq, Real.cosh_eq]
    have hp : Real.exp (2*x) = Real.exp x * Real.exp x := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hm : Real.exp (-(2*x)) = Real.exp (-x) * Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hmul : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hp, hm]
    nlinarith
  have he : (u+s)*(2*d) = 2*((u+s)*d) := by ring
  rw [he, h]
  simp only [mul_zero, Real.cosh_zero]
  ring

theorem integrable_defectFeature (u d : ℝ) (hd : |d| < 1) :
    Integrable (defectFeature u d) := by
  have h2 : |2*d| < 2 := by rw [abs_mul]; norm_num; linarith
  change Integrable (fun s : ℝ => defectFeature u d s)
  simp_rw [defectFeature_expansion]
  exact (((integrable_coshFeature u (2*d) h2).const_mul _).sub
    ((integrable_coshFeature u d (by linarith)).const_mul _)).add
    ((integrable_coshFeature u 0 (by norm_num)).const_mul _)

theorem integral_defectFeature (u d : ℝ) (hd : |d| < 1) :
    (∫ s : ℝ, defectFeature u d s) = diagonalEnergy u d := by
  have h2 : |2*d| < 2 := by rw [abs_mul]; norm_num; linarith
  have hd2 : |d| < 2 := by linarith
  have hi2 : Integrable (fun s : ℝ => (1/2)*coshFeature u (2*d) s) :=
    (integrable_coshFeature u (2*d) h2).const_mul _
  have hid : Integrable (fun s : ℝ => 2*coshFeature u d s) :=
    (integrable_coshFeature u d hd2).const_mul _
  have hi0 : Integrable (fun s : ℝ => (3/2)*coshFeature u 0 s) :=
    (integrable_coshFeature u 0 (by norm_num)).const_mul _
  have hisub : Integrable (fun s : ℝ =>
      (1/2)*coshFeature u (2*d) s - 2*coshFeature u d s) := hi2.sub hid
  simp_rw [defectFeature_expansion]
  rw [integral_add hisub hi0, integral_sub hi2 hid,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_coshFeature u (2*d) h2, integral_coshFeature u d hd2,
    integral_coshFeature u 0 (by norm_num)]
  unfold diagonalEnergy
  have hdq : d^2 < 1 := by nlinarith [sq_abs d, abs_nonneg d]
  have h1 : 1-d^2 ≠ 0 := by linarith
  have h4 : 4-d^2 ≠ 0 := by linarith
  have h24 : 4-(2*d)^2 ≠ 0 := by nlinarith
  simp only [mul_zero, Real.cosh_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
  have he : u*(2*d) = 2*u*d := by ring
  rw [he]
  rw [show 4-(2*d)^2 = 4*(1-d^2) by ring]
  field_simp [h1, h4, h24]
  ring

theorem diagonalEnergy_nonneg (u d : ℝ) (hd : |d| < 1) :
    0 ≤ diagonalEnergy u d := by
  rw [← integral_defectFeature u d hd]
  exact integral_nonneg (fun s => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

end RiemannResearch.Analysis.MontgomeryCoshLaplace
