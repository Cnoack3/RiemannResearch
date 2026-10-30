/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Von Mangoldt series and integrable vertical-line tests

For sigma > 1, the exact norm of each Dirichlet-series term is independent
of the height. Mathlib's actual von Mangoldt summability provider therefore
supplies absolute series-integral interchange against every L1 test.

Source for the statement and intended RH consumer: user-provided explicit-formula
obligation, 30 October 2026, and
RiemannResearch/RH/GaussianPolynomialPrimePowerSummability20261030.md.
Proof infrastructure: Mathlib.NumberTheory.LSeries.Dirichlet and
Mathlib.MeasureTheory.Integral.DominatedConvergence.
No zeta identification is assumed: the actual identity with -zeta'/zeta
comes from Mathlib. No critical-line interchange or contour shift is claimed.
-/

open MeasureTheory
open scoped BigOperators ArithmeticFunction
noncomputable section

namespace RiemannResearch.Analysis.VonMangoldtVerticalIntegral

theorem norm_term_vertical (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term (fun j => (Λ j : ℂ)) ((σ : ℂ)+(t : ℂ)*Complex.I) n‖ =
      ‖LSeries.term (fun j => (Λ j : ℂ)) (σ : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

theorem continuous_term_vertical (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ =>
      LSeries.term (fun j => (Λ j : ℂ)) ((σ : ℂ)+(t : ℂ)*Complex.I) n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC]
    fun_prop (disch := simp [Complex.exp_ne_zero])

theorem integrable_mul_term_vertical {f : ℝ → ℂ} (hf : Integrable f)
    (σ : ℝ) (n : ℕ) :
    Integrable (fun t : ℝ => f t *
      LSeries.term (fun j => (Λ j : ℂ)) ((σ : ℂ)+(t : ℂ)*Complex.I) n) := by
  apply (hf.norm.mul_const ‖LSeries.term (fun j => (Λ j : ℂ)) (σ : ℂ) n‖).mono'
  · exact hf.aestronglyMeasurable.mul (continuous_term_vertical σ n).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [norm_mul, norm_term_vertical]
    exact le_rfl

theorem summable_integral_norm_mul_term {f : ℝ → ℂ} (_hf : Integrable f)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖f t *
      LSeries.term (fun j => (Λ j : ℂ)) ((σ : ℂ)+(t : ℂ)*Complex.I) n‖) := by
  have hs : Summable (fun n : ℕ =>
      ‖LSeries.term (fun j => (Λ j : ℂ)) (σ : ℂ) n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ))
  simpa only [norm_mul, norm_term_vertical, integral_mul_const] using
    hs.mul_left (∫ t : ℝ, ‖f t‖)

theorem integral_mul_LSeries_eq_tsum {f : ℝ → ℂ} (hf : Integrable f)
    {σ : ℝ} (hσ : 1 < σ) :
    (∫ t : ℝ, f t * LSeries (fun j => (Λ j : ℂ)) ((σ : ℂ)+(t : ℂ)*Complex.I)) =
      ∑' n : ℕ, ∫ t : ℝ, f t *
        LSeries.term (fun j => (Λ j : ℂ)) ((σ : ℂ)+(t : ℂ)*Complex.I) n := by
  simp only [LSeries, ← tsum_mul_left]
  exact (integral_tsum_of_summable_integral_norm
    (integrable_mul_term_vertical hf σ) (summable_integral_norm_mul_term hf hσ)).symm

theorem neg_logDeriv_eq_LSeries {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    -logDeriv riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I) =
      LSeries (fun j => (Λ j : ℂ)) ((σ : ℂ)+(t : ℂ)*Complex.I) := by
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (show 1 < ((σ : ℂ)+(t : ℂ)*Complex.I).re by simpa using hσ)
  rw [logDeriv, Pi.div_apply, h]
  ring

theorem integral_mul_neg_logDeriv_eq_tsum {f : ℝ → ℂ} (hf : Integrable f)
    {σ : ℝ} (hσ : 1 < σ) :
    (∫ t : ℝ, f t * (-logDeriv riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I))) =
      ∑' n : ℕ, ∫ t : ℝ, f t *
        LSeries.term (fun j => (Λ j : ℂ)) ((σ : ℂ)+(t : ℂ)*Complex.I) n := by
  simp_rw [neg_logDeriv_eq_LSeries hσ]
  exact integral_mul_LSeries_eq_tsum hf hσ

end RiemannResearch.Analysis.VonMangoldtVerticalIntegral
