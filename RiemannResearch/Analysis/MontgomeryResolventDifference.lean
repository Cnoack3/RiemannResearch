/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryCauchyGram
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
/-! # Mixed differences of the bilateral Laplace resolvent
The exact signed difference is factored before its norm is bounded.
Source: elementary resolvent algebra, applied to Montgomery's Cauchy kernel
(1973, https://websites.umich.edu/~hlm/paircor1.pdf). These are uniform
finite analytic estimates, with no zero-density or pair-correlation input.
-/
noncomputable section
open scoped ComplexConjugate
namespace RiemannResearch.Analysis.MontgomeryResolventDifference
open MontgomeryPoisson
theorem inverse_bound {z : ℂ} (hz : 1 ≤ z.re) :
    ‖z⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ (hz.trans (Complex.re_le_norm z))
theorem inverse_pair_bound {z w : ℂ} {d : ℝ}
    (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (hzi : z.im = d) (hwi : w.im = d) :
    ‖z⁻¹‖ * ‖w⁻¹‖ ≤ 1 / (1+d^2) := by
  have hzq : 1+d^2 ≤ ‖z‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzi]
    nlinarith
  have hwq : 1+d^2 ≤ ‖w‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hwi]
    nlinarith
  have hz1 : 1 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  have hw1 : 1 ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  have hp : 1+d^2 ≤ ‖z‖*‖w‖ := by
    nlinarith [mul_le_mul hzq hwq (by positivity : 0 ≤ 1+d^2) (sq_nonneg ‖z‖),
      sq_nonneg (‖z‖*‖w‖-(1+d^2))]
  rw [norm_inv, norm_inv, ← mul_inv, one_div]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by positivity : 0 < 1+d^2) hp)
theorem inverse_pair_cauchy {z w : ℂ} {d : ℝ}
    (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (hzi : z.im = d) (hwi : w.im = d) :
    ‖z⁻¹‖ * ‖w⁻¹‖ ≤ cauchyWeight d := by
  refine (inverse_pair_bound hz hw hzi hwi).trans ?_
  unfold cauchyWeight
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg d]
theorem inverse_mixed_difference (q a b : ℂ)
    (h0 : q ≠ 0) (ha : q-a ≠ 0) (hb : q-b ≠ 0) (hab : q-a-b ≠ 0) :
    (q-a-b)⁻¹-(q-a)⁻¹-(q-b)⁻¹+q⁻¹ =
      a*b*(q⁻¹*(q-a-b)⁻¹*((q-a)⁻¹+(q-b)⁻¹)) := by
  field_simp
  <;> ring

theorem inverse_mixed_difference_bound (q a b : ℂ) (d : ℝ)
    (h0 : 1 ≤ q.re) (ha : 1 ≤ (q-a).re) (hb : 1 ≤ (q-b).re)
    (hab : 1 ≤ (q-a-b).re)
    (hi0 : q.im = d) (hiab : (q-a-b).im = d) :
    ‖(q-a-b)⁻¹-(q-a)⁻¹-(q-b)⁻¹+q⁻¹‖ ≤
      2 * ‖a‖ * ‖b‖ * cauchyWeight d := by
  have hn {z : ℂ} (h : 1 ≤ z.re) : z ≠ 0 := by
    intro hz; norm_num [hz] at h
  rw [inverse_mixed_difference q a b (hn h0) (hn ha) (hn hb) (hn hab)]
  have hadd : ‖(q-a)⁻¹+(q-b)⁻¹‖ ≤ 2 :=
    (norm_add_le _ _).trans (by linarith [inverse_bound ha, inverse_bound hb])
  have hpair := inverse_pair_cauchy h0 hab hi0 hiab
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ (‖a‖*‖b‖) * (cauchyWeight d * 2) := by
      gcongr
      exact by unfold cauchyWeight; positivity
    _ = _ := by ring

def laplaceKernel (z : ℂ) : ℂ := (2-z)⁻¹ + (2+z)⁻¹

theorem laplaceKernel_eq (z : ℂ) (hz : |z.re| ≤ 1) :
    laplaceKernel z = 4/(4-z^2) := by
  have hzm : 2-z ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith [(abs_le.mp hz).2]
  have hzp : 2+z ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith [(abs_le.mp hz).1]
  have hd : 4-z^2 ≠ 0 := by
    have he : (4-z^2) = (2-z)*(2+z) := by ring
    rw [he]
    exact mul_ne_zero hzm hzp
  unfold laplaceKernel
  field_simp
  <;> ring

def differenceKernel (a b d : ℝ) : ℂ :=
  laplaceKernel ((a+b : ℝ)+Complex.I*d) -
  laplaceKernel ((a : ℂ)+Complex.I*d) -
  laplaceKernel ((b : ℂ)+Complex.I*d) +
  laplaceKernel (Complex.I*d)

theorem differenceKernel_bound (a b d : ℝ) (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/2) :
    ‖differenceKernel a b d‖ ≤ 4 * |a| * |b| * cauchyWeight d := by
  have haa := abs_le.mp ha
  have hbb := abs_le.mp hb
  have hm := inverse_mixed_difference_bound
    (2-Complex.I*d) (a : ℂ) (b : ℂ) (-d)
    (by simp) (by simp; linarith) (by simp; linarith)
    (by simp; linarith) (by simp) (by simp)
  have hp := inverse_mixed_difference_bound
    (2+Complex.I*d) (-a : ℂ) (-b : ℂ) d
    (by simp) (by simp; linarith) (by simp; linarith)
    (by simp; linarith) (by simp) (by simp)
  have he : differenceKernel a b d =
      ((2-Complex.I*d-a-b)⁻¹-(2-Complex.I*d-a)⁻¹-
        (2-Complex.I*d-b)⁻¹+(2-Complex.I*d)⁻¹) +
      ((2+Complex.I*d-(-a)-(-b))⁻¹-(2+Complex.I*d-(-a))⁻¹-
        (2+Complex.I*d-(-b))⁻¹+(2+Complex.I*d)⁻¹) := by
    unfold differenceKernel laplaceKernel
    push_cast
    ring
  rw [he]
  have hw : cauchyWeight (-d) = cauchyWeight d := by
    simp [cauchyWeight]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_neg, hw] at hm hp
  exact (norm_add_le _ _).trans (by linarith)

end RiemannResearch.Analysis.MontgomeryResolventDifference
