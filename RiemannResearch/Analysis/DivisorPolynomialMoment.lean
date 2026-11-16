/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DivisorCoefficientEnergy
import RiemannResearch.Analysis.DirichletPolynomialMeanValue
import RiemannResearch.Analysis.FiniteTwistedMoment
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Actual divisor Dirichlet polynomials and bounded smoothing weights

Source for the fourth-moment application: Chourasiya--Simonic,
https://arxiv.org/html/2507.15184v2, Section 5.1. This module proves the
finite-polynomial input, including the logarithmic degree, uniformly in
the cutoff, interval, and all fixed coefficient weights of norm at most one.
It does not assert a representation of the Riemann zeta function.
-/
noncomputable section
open MeasureTheory Complex Set
open scoped BigOperators

namespace RiemannResearch.Analysis

def criticalDivisorCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.sigma 0 n : ℂ) *
    Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ))

def divisorPolynomial (N : ℕ) (w : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (w n * criticalDivisorCoefficient n) *
    Complex.exp (Complex.I * t * (-Real.log n))

theorem continuous_divisorPolynomial (N : ℕ) (w : ℕ → ℂ) :
    Continuous (divisorPolynomial N w) := by
  unfold divisorPolynomial
  fun_prop

/-- The exact coefficient energy has the actual divisor square. -/
theorem criticalDivisorCoefficient_norm_sq {n : ℕ} (hn : 0 < n) :
    ‖criticalDivisorCoefficient n‖ ^ 2 = (ArithmeticFunction.sigma 0 n : ℝ) ^ 2 / n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ)) =
      (Real.exp (-Real.log (n : ℝ) / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  unfold criticalDivisorCoefficient
  rw [norm_mul, mul_pow, Complex.norm_natCast, hr, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * (-Real.log (n : ℝ) / 2) = -Real.log n by ring,
    Real.exp_neg, Real.exp_log hn0]
  ring

theorem weighted_divisor_coefficient_energy_le (N : ℕ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ 1) :
    (∑ n ∈ Finset.Icc 1 N, ‖w n * criticalDivisorCoefficient n‖ ^ 2) ≤
      (1 + Real.log N) ^ 4 := by
  apply le_trans _ (ArithmeticFunction.sum_sigma_zero_sq_div_le_log_four N)
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, mul_pow, criticalDivisorCoefficient_norm_sq
    (by have := (Finset.mem_Icc.mp hn).1; omega)]
  have hpow := pow_le_pow_left₀ (norm_nonneg (w n)) (hw n hn) 2
  simpa only [one_pow, one_mul] using
    mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤
      (ArithmeticFunction.sigma 0 n : ℝ) ^ 2 / n)

/-- The exact signed interval identity precedes the upper bound. -/
theorem divisorPolynomial_second_moment_identity (N : ℕ) (w : ℕ → ℂ) (H T : ℝ) :
    ((∫ t in H..T, ‖divisorPolynomial N w t‖ ^ 2 : ℝ) : ℂ) =
      (((∑ n ∈ Finset.Icc 1 N, ‖w n * criticalDivisorCoefficient n‖ ^ 2) *
        (T - H) : ℝ) : ℂ) +
      Complex.finiteTwistedOffDiagonal (Finset.Icc 1 N)
        (fun n => w n * criticalDivisorCoefficient n)
        (fun n => -Real.log n) (fun _ => 1) H T := by
  unfold divisorPolynomial
  have h := Complex.integral_finite_sum_norm_sq_diagonal (Finset.Icc 1 N)
    (fun n => w n * criticalDivisorCoefficient n) (fun n => -Real.log n)
    (fun _ => 1) H T continuousOn_const
  simpa only [one_mul, norm_one, one_pow, intervalIntegral.integral_const,
    smul_eq_mul, mul_one, Complex.ofReal_neg] using h

theorem divisorPolynomial_second_moment_le {N : ℕ} (hN : 0 < N)
    (w : ℕ → ℂ) (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ 1)
    {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖divisorPolynomial N w t‖ ^ 2) ≤
      (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) *
        (T - H + N) * (1 + Real.log N) ^ 4 := by
  unfold divisorPolynomial
  exact (dirichlet_polynomial_second_moment_window_le N
    (fun n => w n * criticalDivisorCoefficient n) hHT hN).trans
    (mul_le_mul_of_nonneg_left (weighted_divisor_coefficient_energy_le N w hw)
      (by have := sub_nonneg.mpr hHT; positivity))

/-- The smoothing scale is arbitrary and independent of the finite cutoff. -/
theorem damped_divisorPolynomial_second_moment_le {N : ℕ} (hN : 0 < N)
    {Y : ℝ} (hY : 0 < Y) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖divisorPolynomial N
      (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t‖ ^ 2) ≤
      (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) *
        (T - H + N) * (1 + Real.log N) ^ 4 := by
  apply divisorPolynomial_second_moment_le hN _ _ hHT
  intro n hn
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hY.le)

end RiemannResearch.Analysis
