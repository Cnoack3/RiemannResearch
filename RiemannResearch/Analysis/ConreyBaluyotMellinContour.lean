/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMellinWeight
import RiemannResearch.Analysis.VerticalContourShift
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Group.Integral

/-!
# Positive-contour independence of the Conrey--Baluyot weight

Source for the weight and positive-line shift: S. A. C. Baluyot,
*On the Zeros of Riemann's Zeta-function* (2017), Lemma 3.1.1,
equation (3.1.4), pp. 94--95:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The analytic provider is discharged here: holomorphy on Re z > 0,
a common majorant on every compact positive strip, and absolute integrability.
Consequently the canonical weight inherits every positive-line bound.
The signed negative-contour expansion and density estimate remain open.
-/

open Complex MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

namespace RiemannResearch.Analysis.ConreyBaluyot

def mellinKernel (σ ξ : ℝ) (z : ℂ) : ℂ :=
  Gamma (z + 1) * (riemannZeta ((2 * σ : ℝ) + z) / riemannZeta (2 * σ : ℝ)) *
    riemannZeta (1 + z) * (ξ : ℂ) ^ z

theorem mellinKernel_onLine (σ ξ r t : ℝ) :
    mellinKernel σ ξ ((r : ℂ) + t * I) = mellinIntegrand σ ξ r t := by
  simp only [mellinKernel, mellinIntegrand, mul_comm]

theorem differentiableAt_mellinKernel {σ ξ : ℝ} (hσ : 1 / 2 < σ)
    (hξ : 0 < ξ) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (mellinKernel σ ξ) z := by
  have hg : DifferentiableAt ℂ (fun w : ℂ => Gamma (w + 1)) z := by
    apply (Complex.differentiableAt_Gamma _ ?_).comp z
      (differentiableAt_id.add_const 1)
    intro n hn
    have he := congrArg Complex.re hn
    simp at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hl : DifferentiableAt ℂ (fun w : ℂ => riemannZeta ((2 * σ : ℝ) + w)) z := by
    apply (differentiableAt_riemannZeta ?_).comp z
      (differentiableAt_id.const_add _)
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hr : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (1 + w)) z := by
    apply (differentiableAt_riemannZeta ?_).comp z
      (differentiableAt_id.const_add _)
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hp : DifferentiableAt ℂ (fun w : ℂ => (ξ : ℂ) ^ w) z := by
    have hne : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
    simp only [Complex.cpow_def_of_ne_zero hne]
    fun_prop
  exact ((hg.mul (hl.div_const _)).mul hr).mul hp


/-- A common Cauchy majorant on any compact positive interval, uniform in sigma. -/
theorem exists_mellinKernel_strip_bound {ξ a b : ℝ}
    (hξ : 0 < ξ) (ha : 0 < a) (hb : 0 < b) :
    ∃ B : ℝ, ∀ σ : ℝ, 1 / 2 < σ → ∀ r ∈ uIcc a b, ∀ t : ℝ,
      ‖mellinKernel σ ξ ((r : ℂ) + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹ := by
  let c : ℝ → ℝ := fun r => Real.Gamma (r + 3) * (1 + 1 / r) * ξ ^ r
  have hc : ContinuousOn c (uIcc a b) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le (lt_min ha hb) hr.1
    have hgc : ContinuousAt (fun u : ℝ => Complex.Gamma ((u : ℂ) + 3)) r := by
      apply (Complex.continuousAt_Gamma _ ?_).comp
        (Complex.continuous_ofReal.continuousAt.add continuousAt_const)
      intro n hn
      have he := congrArg Complex.re hn
      simp at he
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hg : ContinuousAt (fun r : ℝ => Real.Gamma (r + 3)) r := by
      simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_add,
        Complex.Gamma_ofReal, Complex.ofReal_re, Function.comp_def] using
          Complex.continuous_re.continuousAt.comp hgc
    have hi : ContinuousAt (fun r : ℝ => 1 + 1 / r) r :=
      continuousAt_const.add (continuousAt_const.div continuousAt_id hr0.ne')
    have hp : ContinuousAt (fun r : ℝ => ξ ^ r) r :=
      (Real.continuous_const_rpow hξ.ne').continuousAt
    exact ((hg.mul hi).mul hp).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn hc
  refine ⟨B, fun σ hσ r hr t => ?_⟩
  have hle : c r ≤ B := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB r hr)
  have hr0 : 0 < r := lt_of_lt_of_le (lt_min ha hb) hr.1
  calc
    _ ≤ c r * (1 + t ^ 2)⁻¹ := by
      simpa [mellinKernel, mellinIntegrand, c, mul_comm] using
        norm_mellinIntegrand_le hσ hξ hr0 t
    _ ≤ B * (1 + t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hle (by positivity)

theorem weightOnLine_eq {σ ξ a b : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (ha : 0 < a) (hb : 0 < b) :
    weightOnLine σ ξ a = weightOnLine σ ξ b := by
  obtain ⟨B, hB⟩ := exists_mellinKernel_strip_bound hξ ha hb
  have he := Complex.integral_vertical_eq_of_cauchy_bound
    (f := mellinKernel σ ξ)
    (fun z hz => differentiableAt_mellinKernel hσ hξ
      (lt_of_lt_of_le (lt_min ha hb) hz.1))
    (by simpa only [mellinKernel_onLine] using integrable_mellinIntegrand hσ hξ ha)
    (by simpa only [mellinKernel_onLine] using integrable_mellinIntegrand hσ hξ hb)
    (hB σ hσ)
  unfold weightOnLine
  congr 1
  simpa [mellinKernel, mellinIntegrand, mul_comm] using he


theorem norm_weight_le_of_posLine {σ ξ r : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (hr : 0 < r) :
    ‖weight σ ξ‖ ≤ Real.Gamma (r + 3) * (1 + 1 / r) * ξ ^ r / 2 := by
  rw [weight, weightOnLine_eq hσ hξ (by norm_num : (0 : ℝ) < 1) hr]
  exact norm_weightOnLine_le hσ hξ hr

theorem norm_weight_le_factorial {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) {n : ℕ} (hn : 1 ≤ n) :
    ‖weight σ ξ‖ ≤ (n + 2).factorial * ξ ^ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hh := norm_weight_le_of_posLine hσ hξ hn0
  have hg : Real.Gamma ((n : ℝ) + 3) = (n + 2).factorial := by
    convert Real.Gamma_nat_eq_factorial (n + 2) using 1 <;> push_cast <;> ring
  rw [hg, Real.rpow_natCast] at hh
  have hi : 1 / (n : ℝ) ≤ 1 := by
    exact (div_le_one hn0).mpr hn1
  have hf : (0 : ℝ) ≤ (n + 2).factorial * ξ ^ n := by positivity
  nlinarith

theorem mellinKernel_conj {σ ξ : ℝ} (hξ : 0 < ξ) (z : ℂ) :
    mellinKernel σ ξ (conj z) = conj (mellinKernel σ ξ z) := by
  have hp : (ξ : ℂ) ^ conj z = conj ((ξ : ℂ) ^ z) := by
    have h := Complex.cpow_conj (ξ : ℂ) z (by
      rw [Complex.arg_ofReal_of_nonneg hξ.le]
      exact Ne.symm Real.pi_ne_zero)
    simpa only [Complex.conj_ofReal] using h
  simp only [mellinKernel, map_mul, map_div₀, ← Complex.Gamma_conj,
    ← riemannZeta_conj, map_add, map_one, Complex.conj_ofReal, hp]

theorem conj_mellinIntegrand {σ ξ r : ℝ} (hξ : 0 < ξ) (t : ℝ) :
    conj (mellinIntegrand σ ξ r t) = mellinIntegrand σ ξ r (-t) := by
  rw [← mellinKernel_onLine, ← mellinKernel_conj hξ, ← mellinKernel_onLine]
  congr 1
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring

theorem conj_weightOnLine {σ ξ r : ℝ} (hξ : 0 < ξ) :
    conj (weightOnLine σ ξ r) = weightOnLine σ ξ r := by
  unfold weightOnLine
  rw [map_mul, map_inv₀]
  have hc : conj (2 * Real.pi : ℂ) = 2 * Real.pi := by
    simp only [map_mul, ← Complex.ofReal_ofNat, Complex.conj_ofReal]
  rw [hc, ← integral_conj]
  congr 1
  simp_rw [conj_mellinIntegrand hξ]
  exact integral_neg_eq_self _ _

theorem weight_im_eq_zero {σ ξ : ℝ} (hξ : 0 < ξ) :
    (weight σ ξ).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_weightOnLine hξ)

end RiemannResearch.Analysis.ConreyBaluyot
