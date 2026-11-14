/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryFormFactor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! # Exact interval averages and signed off-diagonal pairs

Sources for the form-factor convention and Fourier-pairing framework:
Montgomery (1973), https://websites.umich.edu/~hlm/paircor1.pdf;
Carneiro--Milinovich--Ramos, https://arxiv.org/abs/2310.01913, Section 1.2.
The endpoint integration and indexed-diagonal decomposition below are direct
finite identities. They do not assume RH or a pair-correlation limit.

The zero-frequency branch is essential: distinct zero copies can have equal
ordinates. Such terms remain in the signed off-diagonal sum. No injectivity
of the ordinate map, simplicity of zeros, or RH is imposed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.Analysis.MontgomeryFormFactor
open MontgomeryPoisson ZeroOrdinate ActualZeroOrdinate
variable {ι : Type*} [Fintype ι]

/-- Integrated cosine, with its coincident-frequency value retained. -/
def cosineWindow (a b ξ : ℝ) : ℝ :=
  if ξ = 0 then b-a else (Real.sin (b*ξ)-Real.sin (a*ξ))/ξ

theorem integral_cosineWindow (a b ξ : ℝ) :
    (∫ α in a..b, Real.cos (α*ξ)) = cosineWindow a b ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ, cosineWindow]
  · rw [intervalIntegral.integral_comp_mul_right Real.cos hξ, integral_cos]
    simp only [cosineWindow, if_neg hξ, smul_eq_mul]
    ring

@[simp] theorem cosineWindow_zero (a b : ℝ) : cosineWindow a b 0 = b-a := by
  simp [cosineWindow]

theorem pairSum_re_cos (t : ι → ℝ) (u : ℝ) :
    (pairSum t u).re = ∑ i, ∑ j,
      cauchyWeight (t i-t j) * Real.cos (u*(t i-t j)) := by
  have hp (v d : ℝ) : (phase v d).re = Real.cos (v*d) :=
    Complex.exp_ofReal_mul_I_re _
  simp [pairSum, Complex.mul_re, hp]

/-- Exact interval pairing for arbitrary finite ordinates. -/
theorem integral_pairSum_re (t : ι → ℝ) (L a b : ℝ) :
    (∫ α in a..b, (pairSum t (α*L)).re) =
      ∑ i, ∑ j, cauchyWeight (t i-t j) * cosineWindow a b (L*(t i-t j)) := by
  simp_rw [pairSum_re_cos, mul_assoc]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul, integral_cosineWindow]
    · intro j hj
      exact (by fun_prop : Continuous (fun α : ℝ =>
        cauchyWeight (t i-t j) * Real.cos (α*(L*(t i-t j))))).intervalIntegrable a b
  · intro i hi
    exact (by fun_prop : Continuous (fun α : ℝ =>
      ∑ j, cauchyWeight (t i-t j) * Real.cos (α*(L*(t i-t j))))).intervalIntegrable a b

/-- Sum over distinct copy indices, not over distinct ordinates. -/
def offDiagonalWindow (t : ι → ℝ) (L a b : ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j ∈ Finset.univ.erase i,
    cauchyWeight (t i-t j) * cosineWindow a b (L*(t i-t j))

/-- The exact signed off-diagonal remainder. Equal ordinates from distinct
copies remain in the remainder, with window value b-a. -/
theorem interval_pairSum_diagonal (t : ι → ℝ) (L a b : ℝ) :
    (∫ α in a..b, (pairSum t (α*L)).re) =
      (b-a)*(Fintype.card ι : ℝ) + offDiagonalWindow t L a b := by
  classical
  rw [integral_pairSum_re]
  have h (i : ι) :
      (∑ j, cauchyWeight (t i-t j) * cosineWindow a b (L*(t i-t j))) =
        (b-a) + ∑ j ∈ Finset.univ.erase i,
          cauchyWeight (t i-t j) * cosineWindow a b (L*(t i-t j)) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp [cauchyWeight, add_comm]
  simp_rw [h]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, offDiagonalWindow]
  ring

/-- Exact averaged raw form factor, with all signed terms retained. -/
theorem integral_formFactor_diagonal (T a b : ℝ) :
    (∫ α in a..b, formFactor T α) =
      ((b-a)*(Zeta23.Ncount 0 T : ℝ) +
        offDiagonalWindow (copyOrdinate T) (Real.log T) a b) /
      (T*Real.log T/(2*Real.pi)) := by
  unfold formFactor
  rw [intervalIntegral.integral_div, interval_pairSum_diagonal, card_copies]

end RiemannResearch.Analysis.MontgomeryFormFactor
