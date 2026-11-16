/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import RiemannResearch.Analysis.WeightedDivisorMoment
import RiemannResearch.Analysis.MellinGammaEnvelope
import RiemannResearch.Analysis.ZetaSquareMellinWeights
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# The actual infinite divisor-tail Mellin kernel

This is the reflected infinite tail on Re z = -3/4 in the exact
zeta-square remainder decomposition. Its normalized real-line integral
uses the factor 1/(2 pi), accounting for dz = i dv.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory
namespace RiemannResearch.Analysis

def zetaSquareInfiniteTailKernel (N : ℕ) (Y t v : ℝ) : ℂ :=
  Gamma ((-3 / 4 : ℂ) + v * I) * (Y : ℂ) ^ ((-3 / 4 : ℂ) + v * I) *
    Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t + ((-3 / 4 : ℂ) + v * I)) ^ 2 *
      fiveQuarterDivisorTail N (-(t + v))

def zetaSquareInfiniteTailIntegral (N : ℕ) (Y t : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ v : ℝ, zetaSquareInfiniteTailKernel N Y t v

theorem continuous_zetaSquareInfiniteTailKernel_joint (N : ℕ) {Y : ℝ}
    (hY : 0 < Y) :
    Continuous (fun p : ℝ × ℝ => zetaSquareInfiniteTailKernel N Y p.1 p.2) := by
  have htail : Continuous (fiveQuarterDivisorTail N) := by
    have hn (n : ℕ) (t : ℝ) :
        ‖powerWeightedDivisorTerm (-3/4) n t‖ =
          ‖powerWeightedDivisorTerm (-3/4) n 0‖ := by
      simp only [powerWeightedDivisorTerm, norm_mul, Complex.norm_exp,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_zero, Complex.zero_re,
        Complex.neg_re, Complex.neg_im, zero_mul, mul_zero, sub_self,
        neg_zero, Real.exp_zero, mul_one]
    apply continuous_tsum (f := fun n t => if N < n then
      powerWeightedDivisorTerm (-3/4) n t else 0)
      (u := fun n => ‖powerWeightedDivisorTerm (-3/4) n 0‖)
    · intro n
      by_cases h : N < n
      · simp only [h, if_true, powerWeightedDivisorTerm]
        fun_prop
      · simpa only [h, if_false] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
    · exact (summable_fiveQuarterDivisorTerm 0).norm
    · intro n t
      by_cases h : N < n
      · simpa only [h, if_true, hn] using (le_refl ‖powerWeightedDivisorTerm (-3/4) n 0‖)
      · simp [h]
  have hgamma : Continuous (fun p : ℝ × ℝ => Gamma ((-3/4 : ℂ) + p.2 * I)) := by
    have hh : Continuous (fun v : ℝ => Gamma ((-3/4 : ℂ) + v*I)) := by
      simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
        continuous_Gamma_vertical_of_neg_one_lt (a := -3/4) (by norm_num) (by norm_num)
    exact hh.comp continuous_snd
  have hpow : Continuous (fun p : ℝ × ℝ => (Y : ℂ) ^ ((-3/4 : ℂ) + p.2 * I)) :=
    (show Continuous (fun p : ℝ × ℝ => (-3/4 : ℂ) + p.2 * I) from by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
  have hchi : Continuous (fun p : ℝ × ℝ =>
      Zeta23.XiPrime.chiFE ((1/2 : ℂ) + I * p.1 + ((-3/4 : ℂ) + p.2 * I))) := by
    have he (p : ℝ × ℝ) :
        (1/2 : ℂ) + I * p.1 + ((-3/4 : ℂ) + p.2 * I) =
          (-1/4 : ℂ) + I * ((p.1 + p.2 : ℝ) : ℂ) := by
      push_cast
      ring
    simp_rw [he]
    have hh : Continuous (fun w : ℝ => Zeta23.XiPrime.chiFE ((-1/4 : ℂ) + I*w)) := by
      simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat,
        Complex.ofReal_one] using
        SymmetricZetaRatio.continuous_chiFE_vertical (σ := -1/4) (by norm_num)
    exact hh.comp (continuous_fst.add continuous_snd)
  exact ((hgamma.mul hpow).mul (hchi.pow 2)).mul
    (htail.comp (continuous_fst.add continuous_snd).neg)

end RiemannResearch.Analysis
