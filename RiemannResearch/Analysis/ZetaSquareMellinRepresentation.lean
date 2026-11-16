/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Push
import RiemannResearch.Analysis.ActualZetaSquareMellinTail
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellin
import RiemannResearch.Analysis.DampedDivisorSeries
import RiemannResearch.Analysis.DivisorLSeries
/-!
# Exact Mellin representation of the exponentially smoothed divisor series

For every positive real smoothing scale and every real height, the actual
ordinary divisor series is the integral of the actual zeta-square kernel
on any vertical line to the right of one half. Absolute convergence of the
divisor L-series and Gamma integrability justify the interchange. The scalar
complex Mellin inversion theorem supplies the exponential factor.

The Estermann identity also identifies the actual kernel on the entire
complex plane, so its existing contour and strip estimates can be reused.
-/

open Complex MeasureTheory Filter
open scoped BigOperators
noncomputable section
namespace RiemannResearch.Analysis

/-- Exact modulus-one specialization, valid at every complex kernel argument. -/
theorem zetaSquareMellinKernel_eq_estermannMellinKernel {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) (z : ℂ) :
    zetaSquareMellinKernel Y t z =
      ConreyBaluyot.estermannMellinKernel (0 : ZMod 1)
        ((1 / 2 : ℂ) + I * t) ((1 / 2 : ℂ) + I * t) (Y : ℂ)⁻¹ z := by
  have ha : (Y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hY.le]
    exact Real.pi_pos.ne
  simp only [ConreyBaluyot.estermannMellinKernel,
    ConreyBaluyot.estermann_mod_one_eq_zeta_product,
    Complex.inv_cpow _ _ ha, Complex.cpow_neg, inv_inv,
    zetaSquareMellinKernel, pow_two]
  rw [add_comm z]

/-- Absolute integrability on every initial Mellin line, with no analytic premise. -/
theorem integrable_zetaSquareMellinKernel_vertical {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Integrable (fun v : ℝ => zetaSquareMellinKernel Y t ((c : ℂ) + I * v)) := by
  simp_rw [zetaSquareMellinKernel_eq_estermannMellinKernel hY]
  apply ConreyBaluyot.integrable_estermannMellinKernel_vertical
  · simpa only [← Complex.ofReal_inv, Complex.ofReal_re] using inv_pos.mpr hY
  · linarith
  · norm_num [Complex.mul_re]
    linarith
  · norm_num [Complex.mul_re]
    linarith

private theorem norm_LSeries_term_vertical (a : ℕ → ℂ) (s : ℂ) (c v : ℝ) (n : ℕ) :
    ‖LSeries.term a ((c : ℂ) + I * v + s) n‖ =
      ‖LSeries.term a ((c : ℂ) + s) n‖ := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  simp [hn, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hn', Complex.mul_re]

private theorem continuous_LSeries_term_vertical (a : ℕ → ℂ) (s : ℂ)
    (c : ℝ) (n : ℕ) :
    Continuous (fun v : ℝ => LSeries.term a ((c : ℂ) + I * v + s) n) := by
  by_cases hn : n = 0
  · simpa [hn] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [LSeries.term_def, hn, if_false]
  apply Continuous.div continuous_const
  · exact (by fun_prop : Continuous (fun v : ℝ => (c : ℂ) + I * v + s)).const_cpow
      (.inl hn')
  · intro v
    rw [Complex.cpow_def_of_ne_zero hn']
    exact Complex.exp_ne_zero _

private theorem integral_mul_LSeries_eq_tsum_integral (a : ℕ → ℂ) (s : ℂ)
    {c : ℝ} (hs : LSeriesSummable a ((c : ℂ) + s))
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ v : ℝ, f v * LSeries a ((c : ℂ) + I * v + s)) =
      ∑' n : ℕ, ∫ v : ℝ, f v * LSeries.term a ((c : ℂ) + I * v + s) n := by
  have hint (n : ℕ) : Integrable (fun v : ℝ =>
      f v * LSeries.term a ((c : ℂ) + I * v + s) n) := by
    refine (hf.norm.mul_const ‖LSeries.term a ((c : ℂ) + s) n‖).mono'
      (hf.aestronglyMeasurable.mul
        (continuous_LSeries_term_vertical a s c n).aestronglyMeasurable) ?_
    exact Eventually.of_forall fun v => by
      rw [norm_mul, norm_LSeries_term_vertical]
  have hsum : Summable (fun n : ℕ => ∫ v : ℝ,
      ‖f v * LSeries.term a ((c : ℂ) + I * v + s) n‖) := by
    simp_rw [norm_mul, norm_LSeries_term_vertical, integral_mul_const]
    exact hs.norm.mul_left _
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  apply integral_congr_ae
  filter_upwards with v
  change f v * (∑' n : ℕ, LSeries.term a ((c : ℂ) + I * v + s) n) = _
  rw [tsum_mul_left]

private theorem LSeries_term_add_shift (a : ℕ → ℂ) (s z : ℂ) (n : ℕ) :
    LSeries.term a (z + s) n =
      (n : ℂ) ^ (-z) * LSeries.term a s n := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [LSeries.term_def, hn, if_false, Complex.cpow_add _ _ hn',
    Complex.cpow_neg, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem criticalDivisorCoefficient_mul_phase_eq_term (n : ℕ) (t : ℝ) :
    criticalDivisorCoefficient n * exp (I * t * (-Real.log n)) =
      LSeries.term (fun n => (ArithmeticFunction.sigma 0 n : ℂ))
        ((1 / 2 : ℂ) + I * t) n := by
  by_cases hn : n = 0
  · simp [hn, criticalDivisorCoefficient]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [LSeries.term_def, hn, if_false, criticalDivisorCoefficient,
    Complex.cpow_def_of_ne_zero hn', div_eq_mul_inv, ← Complex.exp_neg, mul_assoc,
    ← Complex.exp_add]
  congr 2
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  push_cast
  ring


private theorem dampedLSeries_eq_mellinIntegral (a : ℕ → ℂ) (s : ℂ)
    {Y : ℝ} (hY : 0 < Y) {c : ℝ} (hc : 0 < c)
    (hs : LSeriesSummable a ((c : ℂ) + s)) :
    (∑' n : ℕ, (Real.exp (-(n : ℝ) / Y) : ℂ) * LSeries.term a s n) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ v : ℝ, Gamma ((c : ℂ) + I * v) * (Y : ℂ) ^ ((c : ℂ) + I * v) *
          LSeries a ((c : ℂ) + I * v + s) := by
  have ha : (Y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hY.le]
    exact Real.pi_pos.ne
  have hp (z : ℂ) : (Y : ℂ)⁻¹ ^ (-z) = (Y : ℂ) ^ z := by
    rw [Complex.inv_cpow _ _ ha, Complex.cpow_neg, inv_inv]
  have hlam : 0 < ((Y : ℂ)⁻¹).re := by
    simpa only [← Complex.ofReal_inv, Complex.ofReal_re] using inv_pos.mpr hY
  have hf := Complex.integrable_gamma_mul_cpow_neg hlam hc
  simp_rw [hp] at hf
  rw [integral_mul_LSeries_eq_tsum_integral a s hs hf, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hi := Complex.exponential_eq_mellin_integral hlam hc hn'
  simp_rw [hp] at hi
  simp only [Complex.ofReal_natCast] at hi
  have hdamp : exp (-(Y : ℂ)⁻¹ * (n : ℂ)) =
      (Real.exp (-(n : ℝ) / Y) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hdamp] at hi
  rw [hi]
  simp_rw [LSeries_term_add_shift, ← mul_assoc]
  rw [integral_mul_const]
  ring

/-- The actual smoothed divisor series equals the zeta-square Mellin integral
for every real scale `Y > 0`, real height, and initial line `c > 1/2`. -/
theorem dampedDivisorSeries_eq_mellinIntegral
    {Y : ℝ} (hY : 0 < Y) (t : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    dampedDivisorSeries Y t =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ v : ℝ, zetaSquareMellinKernel Y t ((c : ℂ) + I * v) := by
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.sigma 0 n : ℂ)
  let s : ℂ := (1 / 2 : ℂ) + I * t
  have he (n : ℕ) : dampedDivisorTerm Y n t =
      (Real.exp (-((n + 1 : ℕ) : ℝ) / Y) : ℂ) * LSeries.term a s (n + 1) := by
    rw [dampedDivisorTerm, mul_assoc, criticalDivisorCoefficient_mul_phase_eq_term]
  have hsum : Summable (fun n : ℕ =>
      (Real.exp (-(n : ℝ) / Y) : ℂ) * LSeries.term a s n) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [← he] using (summable_norm_dampedDivisorTerm hY t).of_norm
  have hs : 1 < ((c : ℂ) + s).re := by
    dsimp [s]
    norm_num
    linarith
  calc
    dampedDivisorSeries Y t =
        ∑' n : ℕ, (Real.exp (-(n : ℝ) / Y) : ℂ) * LSeries.term a s n := by
      rw [hsum.tsum_eq_zero_add]
      simp only [LSeries.term_zero, mul_zero, zero_add]
      simp only [dampedDivisorSeries, he]
    _ = (1 / (2 * (Real.pi : ℂ))) *
        ∫ v : ℝ, Gamma ((c : ℂ) + I * v) * (Y : ℂ) ^ ((c : ℂ) + I * v) *
          LSeries a ((c : ℂ) + I * v + s) :=
      dampedLSeries_eq_mellinIntegral a s hY (by linarith) (divisorLSeriesSummable hs)
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with v
      rw [← riemannZeta_sq_eq_divisorLSeries (by
        dsimp [s]
        norm_num
        linarith)]
      simp only [zetaSquareMellinKernel, s, add_comm ((c : ℂ) + I * v)]

end RiemannResearch.Analysis
