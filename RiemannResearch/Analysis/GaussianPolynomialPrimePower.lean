/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GaussianLogDecay
import RiemannResearch.Analysis.GaussianPolynomialFourier
import RiemannResearch.Analysis.GaussianPolynomialFourierGrowth
import RiemannResearch.Analysis.GaussianPolynomialStrip
import RiemannResearch.Analysis.VonMangoldtVerticalIntegral
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absolute prime-power summability for the actual Gaussian transform

For every R > 0, real center and real polynomial, the integral-defined
GaussianPolynomialFourier.transform has inverse-power decay at both signs
of log n. The full complex von Mangoldt contribution is absolutely summable.
Higher prime powers and both signed transform values are retained exactly.

The right-line interchange is specialized to the entire Gaussian-polynomial
test at t + i*(1/2-sigma), with its integrability discharged by the existing
horizontal-strip module. The shifted-transform evaluation and completed-zeta
contour argument remain separate obligations.

Source: user's 30 October 2026 comparison argument and
RiemannResearch/RH/GaussianPolynomialPrimePowerSummability20261030.md.
The actual envelope is GaussianPolynomialFourierGrowth.norm_transform_test_le;
the arithmetic comparison and p-series infrastructure come from Mathlib.
No RH, zero-location or positivity hypothesis is used.
-/

open MeasureTheory
open scoped BigOperators ArithmeticFunction
noncomputable section

namespace RiemannResearch.Analysis.GaussianPolynomialPrimePower
open GaussianPolynomialFourier GaussianPolynomialFourierGrowth

def decayConstant (R : ℝ) (B : Polynomial ℝ) (k : ℕ) : ℝ :=
  frequencyConstant R B *
    Real.exp (R*(((frequencyPolynomial R B).natDegree : ℝ)+(k : ℝ))^2)

theorem decayConstant_nonneg (R : ℝ) (B : Polynomial ℝ) (k : ℕ) :
    0 ≤ decayConstant R B k :=
  mul_nonneg (frequencyConstant_nonneg R B) (Real.exp_nonneg _)

theorem norm_transform_le_exp {R : ℝ} (hR : 0 < R)
    (τ u : ℝ) (B : Polynomial ℝ) (k : ℕ) :
    ‖transform (test R τ B) u‖ ≤ decayConstant R B k * Real.exp (-(k : ℝ)*|u|) := by
  have h := GaussianLogDecay.polynomial_gaussian_le hR
    (frequencyPolynomial R B).natDegree (k : ℝ) (abs_nonneg u)
  have he : -(1/(4*R))*u^2 = -|u|^2/(4*R) := by rw [sq_abs]; ring
  calc
    _ ≤ frequencyConstant R B * (1+|u|)^(frequencyPolynomial R B).natDegree *
        Real.exp (-(1/(4*R))*u^2) := norm_transform_test_le hR τ u B
    _ ≤ decayConstant R B k * Real.exp (-(k : ℝ)*|u|) := by
      rw [he, mul_assoc]
      simpa only [decayConstant, mul_assoc] using
        mul_le_mul_of_nonneg_left h (frequencyConstant_nonneg R B)

theorem norm_transform_log_le {R : ℝ} (hR : 0 < R)
    (τ : ℝ) (B : Polynomial ℝ) (k n : ℕ) (hn : 0 < n) :
    ‖transform (test R τ B) (Real.log n)‖ ≤ decayConstant R B k / (n : ℝ)^k := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  simpa only [abs_of_nonneg (Real.log_nonneg hn1),
    GaussianLogDecay.exp_neg_nat_mul_log hnR, div_eq_mul_inv] using
    norm_transform_le_exp hR τ (Real.log n) B k

theorem norm_transform_neg_log_le {R : ℝ} (hR : 0 < R)
    (τ : ℝ) (B : Polynomial ℝ) (k n : ℕ) (hn : 0 < n) :
    ‖transform (test R τ B) (-Real.log n)‖ ≤ decayConstant R B k / (n : ℝ)^k := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  simpa only [abs_neg, abs_of_nonneg (Real.log_nonneg hn1),
    GaussianLogDecay.exp_neg_nat_mul_log hnR, div_eq_mul_inv] using
    norm_transform_le_exp hR τ (-Real.log n) B k

def absoluteTerm (R τ : ℝ) (B : Polynomial ℝ) (n : ℕ) : ℝ :=
  (Λ n : ℝ) / Real.sqrt n *
    (‖transform (test R τ B) (Real.log n)‖ +
      ‖transform (test R τ B) (-Real.log n)‖)

theorem absoluteTerm_nonneg (R τ : ℝ) (B : Polynomial ℝ) (n : ℕ) :
    0 ≤ absoluteTerm R τ B n := by
  exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.sqrt_nonneg _)) (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem absoluteTerm_le {R : ℝ} (hR : 0 < R)
    (τ : ℝ) (B : Polynomial ℝ) (n : ℕ) :
    absoluteTerm R τ B n ≤ 2*decayConstant R B 3 * ((n : ℝ)^2)⁻¹ := by
  by_cases hn : n = 0
  · subst n
    simp [absoluteTerm]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn0)
  have hw : (Λ n : ℝ) / Real.sqrt n ≤ (n : ℝ) := by
    apply le_trans (div_le_self ArithmeticFunction.vonMangoldt_nonneg
      (Real.one_le_sqrt.mpr hn1))
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (le_trans (Real.log_le_sub_one_of_pos hnR) (by linarith))
  have hg : ‖transform (test R τ B) (Real.log n)‖ +
      ‖transform (test R τ B) (-Real.log n)‖ ≤
        2*decayConstant R B 3 / (n : ℝ)^3 := by
    have h1 := norm_transform_log_le hR τ B 3 n hn0
    have h2 := norm_transform_neg_log_le hR τ B 3 n hn0
    calc
      _ ≤ decayConstant R B 3 / (n : ℝ)^3 + decayConstant R B 3 / (n : ℝ)^3 :=
        add_le_add h1 h2
      _ = _ := by ring
  calc
    _ ≤ (n : ℝ)*(2*decayConstant R B 3 / (n : ℝ)^3) :=
      mul_le_mul hw hg (by positivity) (by positivity)
    _ = _ := by field_simp [ne_of_gt hnR]

theorem summable_absoluteTerm {R : ℝ} (hR : 0 < R) (τ : ℝ) (B : Polynomial ℝ) :
    Summable (absoluteTerm R τ B) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ)^2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  exact (hs.mul_left (2*decayConstant R B 3)).of_nonneg_of_le
    (absoluteTerm_nonneg R τ B) (absoluteTerm_le hR τ B)

def term (R τ : ℝ) (B : Polynomial ℝ) (n : ℕ) : ℂ :=
  ((Λ n / Real.sqrt n : ℝ) : ℂ) *
    (transform (test R τ B) (Real.log n) +
      transform (test R τ B) (-Real.log n))

theorem norm_term_le (R τ : ℝ) (B : Polynomial ℝ) (n : ℕ) :
    ‖term R τ B n‖ ≤ absoluteTerm R τ B n := by
  dsimp [term, absoluteTerm]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _)
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))

theorem summable_term {R : ℝ} (hR : 0 < R) (τ : ℝ) (B : Polynomial ℝ) :
    Summable (term R τ B) :=
  (summable_absoluteTerm hR τ B).of_norm_bounded (norm_term_le R τ B)

theorem term_eq_zero_of_not_prime_pow (R τ : ℝ) (B : Polynomial ℝ)
    {n : ℕ} (hn : ¬IsPrimePow n) : term R τ B n = 0 := by
  simp [term, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]

theorem term_prime_pow (R τ : ℝ) (B : Polynomial ℝ)
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    term R τ B (p^k) =
      ((Real.log p / Real.sqrt (p^k : ℕ) : ℝ) : ℂ) *
        (transform (test R τ B) (Real.log (p^k : ℕ)) +
          transform (test R τ B) (-Real.log (p^k : ℕ))) := by
  simp only [term, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

theorem integral_right_neg_logDeriv_eq_tsum {R σ : ℝ} (hR : 0 < R) (hσ : 1 < σ)
    (τ : ℝ) (B : Polynomial ℝ) :
    (∫ t : ℝ, GaussianPolynomialStrip.test R τ (B.map Complex.ofRealHom)
      ((t : ℂ)+((1/2-σ : ℝ) : ℂ)*Complex.I) *
      (-logDeriv riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I))) =
      ∑' n : ℕ, ∫ t : ℝ,
        GaussianPolynomialStrip.test R τ (B.map Complex.ofRealHom)
          ((t : ℂ)+((1/2-σ : ℝ) : ℂ)*Complex.I) *
        LSeries.term (fun j => (Λ j : ℂ)) ((σ : ℂ)+(t : ℂ)*Complex.I) n :=
  VonMangoldtVerticalIntegral.integral_mul_neg_logDeriv_eq_tsum
    (GaussianPolynomialStrip.integrable_horizontal hR τ (1/2-σ) (B.map Complex.ofRealHom)) hσ

end RiemannResearch.Analysis.GaussianPolynomialPrimePower
