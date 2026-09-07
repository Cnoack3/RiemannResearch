/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact Fourier integral of an even exponential kernel

The proof adapts `Zeta23/ExplicitFormula.lean`, lines 430--487, from the
Apache-2.0 Zeta23 source supplied to this workspace. That proof treats a=1/2;
this module retains its half-line integration argument and proves every a>0.
The source supports the proof strategy and Fourier normalization.
-/

open MeasureTheory Complex Set

namespace RiemannResearch.Analysis.GammaLaplaceKernel

noncomputable def evenExponential (a u : ℝ) : ℂ := Real.exp (-a * |u|)

private theorem kernel_eq_left (a r : ℝ) :
    EqOn (fun u : ℝ => evenExponential a u * Complex.exp (-I * r * u))
      (fun u : ℝ => Complex.exp (((a : ℂ) - I * r) * u)) (Iic 0) := by
  intro u hu
  simp only [mem_Iic] at hu
  simp only [evenExponential, abs_of_nonpos hu, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem kernel_eq_right (a r : ℝ) :
    EqOn (fun u : ℝ => evenExponential a u * Complex.exp (-I * r * u))
      (fun u : ℝ => Complex.exp ((-(a : ℂ) - I * r) * u)) (Ioi 0) := by
  intro u hu
  simp only [mem_Ioi] at hu
  simp only [evenExponential, abs_of_pos hu, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Absolute integrability of the actual Fourier integrand, proved on both
half-lines with their correct signs. -/
theorem integrable_exp_neg_abs_mul {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Integrable (fun u : ℝ => evenExponential a u * Complex.exp (-I * r * u)) := by
  have hleft : IntegrableOn (fun u : ℝ => Complex.exp (((a : ℂ) - I * r) * u))
      (Iic 0) := integrableOn_exp_mul_complex_Iic (by simpa using ha) 0
  have hright : IntegrableOn (fun u : ℝ => Complex.exp ((-(a : ℂ) - I * r) * u))
      (Ioi 0) := integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos ha) 0
  have h := (hleft.congr_fun (kernel_eq_left a r).symm measurableSet_Iic).union
    (hright.congr_fun (kernel_eq_right a r).symm measurableSet_Ioi)
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem integrable_evenExponential {a : ℝ} (ha : 0 < a) :
    Integrable (evenExponential a) := by
  simpa using integrable_exp_neg_abs_mul ha 0

/-- In the paper's unscaled Fourier variable,
`∫ exp(-a|u|) exp(-iru) du = 2a/(a²+r²)`. -/
theorem integral_exp_neg_abs_mul {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (∫ u : ℝ, evenExponential a u * Complex.exp (-I * r * u)) =
      (2 * a : ℂ) / ((a : ℂ) ^ 2 + (r : ℂ) ^ 2) := by
  have hleft : IntegrableOn (fun u : ℝ => Complex.exp (((a : ℂ) - I * r) * u))
      (Iic 0) := integrableOn_exp_mul_complex_Iic (by simpa using ha) 0
  have hright : IntegrableOn (fun u : ℝ => Complex.exp ((-(a : ℂ) - I * r) * u))
      (Ioi 0) := integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos ha) 0
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0)
    (hleft.congr_fun (kernel_eq_left a r).symm measurableSet_Iic)
    (hright.congr_fun (kernel_eq_right a r).symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Iic (kernel_eq_left a r),
    setIntegral_congr_fun measurableSet_Ioi (kernel_eq_right a r),
    integral_exp_mul_complex_Iic (by simpa using ha) 0,
    integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos ha) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hleft0 : (a : ℂ) - I * r ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact ha.ne' hr
  have hright0 : -(a : ℂ) - I * r ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact ha.ne' hr
  have hden : (a : ℂ) ^ 2 + (r : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < a ^ 2 + r ^ 2 by nlinarith [sq_pos_of_pos ha, sq_nonneg r]))
  rw [div_add_div _ _ hleft0 hright0,
    div_eq_div_iff (mul_ne_zero hleft0 hright0) hden]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The exact Lorentzian term in the real digamma increment. -/
theorem integral_evenExponential_two_mul {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (∫ u : ℝ, evenExponential (2 * b) u * Complex.exp (-I * r * u)) =
      (b : ℂ) / ((b : ℂ) ^ 2 + ((r : ℂ) / 2) ^ 2) := by
  rw [integral_exp_neg_abs_mul (by positivity : 0 < 2 * b)]
  push_cast
  have hden : (b : ℂ) ^ 2 + ((r : ℂ) / 2) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < b ^ 2 + (r / 2) ^ 2 by
      nlinarith [sq_pos_of_pos hb, sq_nonneg (r / 2)]))
  have hfactor : (2 * (b : ℂ)) ^ 2 + (r : ℂ) ^ 2 =
      4 * ((b : ℂ) ^ 2 + ((r : ℂ) / 2) ^ 2) := by ring
  rw [hfactor, div_eq_div_iff (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hden) hden]
  ring

end RiemannResearch.Analysis.GammaLaplaceKernel
