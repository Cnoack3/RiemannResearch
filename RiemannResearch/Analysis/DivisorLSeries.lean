/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # The absolutely convergent divisor series for the square of zeta -/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Analysis

/-- The divisor-count function is the arithmetic convolution of two zeta
arithmetic functions, with coefficients in the complex numbers. -/
theorem divisorArithmeticFunction_eq_zeta_mul :
    (ArithmeticFunction.sigma 0 : ArithmeticFunction ℂ) =
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) := by
  have hpow : ArithmeticFunction.pow 0 = ArithmeticFunction.zeta := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp
    · simp [ArithmeticFunction.pow_apply, ArithmeticFunction.zeta_apply, hn]
  rw [← ArithmeticFunction.natCoe_mul, ← ArithmeticFunction.zeta_mul_pow_eq_sigma, hpow]

/-- Absolute convergence of the divisor Dirichlet series throughout
the open half-plane of real part greater than one. -/
theorem divisorLSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.sigma 0 n : ℂ)) s := by
  have hz := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hm := ArithmeticFunction.LSeriesSummable_mul
    (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
    (g := (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) hz hz
  rw [← divisorArithmeticFunction_eq_zeta_mul] at hm
  exact hm

/-- The exact ordinary divisor L-series equals the square of Riemann zeta;
no convergence or Euler-product hypothesis is supplied by the caller. -/
theorem riemannZeta_sq_eq_divisorLSeries {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 2 =
      LSeries (fun n => (ArithmeticFunction.sigma 0 n : ℂ)) s := by
  have hz := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hm := ArithmeticFunction.LSeries_mul'
    (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
    (g := (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) hz hz
  rw [← divisorArithmeticFunction_eq_zeta_mul] at hm
  change LSeries (fun n => (ArithmeticFunction.sigma 0 n : ℂ)) s =
    LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) s *
      LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) s at hm
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hm
  simpa only [pow_two] using hm.symm

end RiemannResearch.Analysis
