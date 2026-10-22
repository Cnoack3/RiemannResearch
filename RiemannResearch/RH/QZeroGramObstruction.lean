/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ArgumentDoublingGenerators
import RiemannResearch.RH.ParetoMellinFiniteGram
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
/-!
# Actual Q zero-displacement and finite zero-Gram certificates

Source: user-directed determinant-ratio and zero-ordinate argument,
21 October 2026. These are consequences of the existing Mellin separator,
complete Q/P norm comparison, and the actual continuous kernel integrals.
No zero limit, RH, Cauchy determinant product, or Burnol rate is assumed.
-/

open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.QZeroGramObstruction
open ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer Pareto
open Pareto.CoefficientStabilization

private theorem one_mellin (s : ℂ) (hs : 0 < s.re) :
    paretoMellin hilbertOne s = 1 / s := by
  rw [paretoMellin_eq_step_integral]
  have he : (∫ x in Ioi (1 : ℝ), (hilbertSequence hilbertOne ⌊x⌋₊ : ℂ) *
      (x : ℂ)^(-s - 1)) = ∫ x in Ioi (1 : ℝ), (x : ℂ)^(-s - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    have hx' : (1 : ℝ) < x := hx
    have hf : 1 ≤ ⌊x⌋₊ :=
      (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x)).2 (by simpa using hx'.le)
    rw [hilbertOne_sequence]
    simp [zeroAnchor, show ⌊x⌋₊ ≠ 0 by omega]
  rw [he, integral_Ioi_cpow_of_lt (by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith) (by norm_num)]
  simp

theorem zero_displacement_bound (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    2 * s.re - 1 ≤ zetaTwo * Complex.normSq s * ‖qOne - f‖ ^ 2 := by
  have h := closedSpace_mellin_distance_sq_lower_bound s hs hs1 hz
    hilbertOne (toPareto f) (toPareto_mem_closedSpace hf)
  rw [one_mellin s (by linarith), norm_div, norm_one, div_pow, one_pow] at h
  have ht := toPareto_norm_sq_le (qOne - f)
  have he : toPareto (qOne - f) = hilbertOne - toPareto f := by
    change toParetoLinear (qOne - f) = _
    rw [map_sub]
    exact congrArg (· - toPareto f) toPareto_qOne
  rw [he] at ht
  have hn : 0 < ‖s‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hz0
    simp [hz0] at hs
    linarith
  rw [mul_one_div] at h
  have hh : 2 * s.re - 1 ≤ ‖hilbertOne - toPareto f‖ ^ 2 * ‖s‖ ^ 2 :=
    (div_le_iff₀ hn).mp h
  rw [Complex.sq_norm] at hh
  nlinarith [Complex.normSq_nonneg s]

theorem zero_floor (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    (2 * s.re - 1) / (zetaTwo * Complex.normSq s) ≤ ‖qOne - f‖ ^ 2 := by
  have hn : s ≠ 0 := by intro h; simp [h] at hs; linarith
  exact (div_le_iff₀ (mul_pos zetaTwo_pos (Complex.normSq_pos.mpr hn))).mpr
    (by nlinarith [zero_displacement_bound s hs hs1 hz f hf])


theorem zero_horizontal_bound (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) (f : QHilbert)
    (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    |s.re - 1 / 2| ≤ (zetaTwo / 2) * (1 + s.im ^ 2) * ‖qOne - f‖ ^ 2 := by
  have hpos : 0 ≤ zetaTwo * ‖qOne - f‖ ^ 2 :=
    mul_nonneg zetaTwo_pos.le (sq_nonneg _)
  by_cases hright : (1 / 2 : ℝ) < s.re
  · have hsne : s ≠ 1 := by intro h; simp [h] at hs1
    have h := zero_displacement_bound s hright hsne hz f hf
    have hn : Complex.normSq s ≤ 1 + s.im ^ 2 := by
      rw [Complex.normSq_apply]
      nlinarith [mul_nonneg hs0.le (by linarith : 0 ≤ 1 - s.re)]
    have hm := mul_le_mul_of_nonneg_right hn hpos
    rw [abs_of_nonneg (by linarith : 0 ≤ s.re - 1 / 2)]
    nlinarith
  · by_cases heq : s.re = 1 / 2
    · rw [heq, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg (div_nonneg zetaTwo_pos.le (by norm_num))
        (by positivity)) (sq_nonneg _)
    · have hleft : s.re < 1 / 2 := lt_of_le_of_ne (le_of_not_gt hright) heq
      have ht : (1 / 2 : ℝ) < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
      have htne : 1 - s ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.one_re] at this
        linarith
      have hnonneg : ∀ n : ℕ, s ≠ -(n : ℂ) := by
        intro n hn
        have h := congrArg Complex.re hn
        simp only [Complex.neg_re, Complex.natCast_re] at h
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hsz1 : s ≠ 1 := by intro h; simp [h] at hs1
      have htz : riemannZeta (1 - s) = 0 := by
        rw [riemannZeta_one_sub hnonneg hsz1, hz, mul_zero]
      have h := zero_displacement_bound (1 - s) ht htne htz f hf
      have hn : Complex.normSq (1 - s) ≤ 1 + s.im ^ 2 := by
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
          Complex.sub_im, Complex.one_im]
        nlinarith [mul_nonneg hs0.le (by linarith : 0 ≤ 1 - s.re)]
      have hm := mul_le_mul_of_nonneg_right hn hpos
      simp only [Complex.sub_re, Complex.one_re] at h
      rw [abs_of_nonpos (by linarith : s.re - 1 / 2 ≤ 0)]
      nlinarith


theorem residual_mellin_eq_one_div (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    paretoMellin (toPareto (qOne - f)) s = 1 / s := by
  have he : toPareto (qOne - f) = hilbertOne - toPareto f := by
    change toParetoLinear (qOne - f) = _
    rw [map_sub]
    exact congrArg (· - toPareto f) toPareto_qOne
  rw [he]
  change paretoMellinContinuous s hs (hilbertOne - toPareto f) = _
  rw [map_sub]
  change paretoMellin hilbertOne s - paretoMellin (toPareto f) s = _
  rw [one_mellin s (by linarith)]
  have hz0 := paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) s hs hs1 hz
    (closedSpace_le_legalClosure (toPareto_mem_closedSpace hf))
  rw [hz0, sub_zero]

theorem zeroGram_inverse_error_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℂ) (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hs1 : ∀ i, s i ≠ 1) (hz : ∀ i, riemannZeta (s i) = 0)
    (hdet : (mellinCauchyGram s).det ≠ 0)
    (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    (dotProduct (fun i => starRingEnd ℂ (1 / s i))
      ((mellinCauchyGram s)⁻¹.mulVec (fun i => 1 / s i))).re ≤
      zetaTwo * ‖qOne - f‖ ^ 2 := by
  have h := finiteMellinKernel_inverse_lower_bound (toPareto (qOne - f)) s hs hdet
  simp_rw [residual_mellin_eq_one_div _ (hs _) (hs1 _) (hz _) f hf] at h
  exact h.trans (toPareto_norm_sq_le (qOne - f))

theorem zeroGram_inverse_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℂ) (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hs1 : ∀ i, s i ≠ 1) (hz : ∀ i, riemannZeta (s i) = 0)
    (hdet : (mellinCauchyGram s).det ≠ 0)
    (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    (dotProduct (fun i => starRingEnd ℂ (1 / s i))
      ((mellinCauchyGram s)⁻¹.mulVec (fun i => 1 / s i))).re / zetaTwo ≤
      ‖qOne - f‖ ^ 2 :=
  (div_le_iff₀ zetaTwo_pos).mpr
    (by nlinarith [zeroGram_inverse_error_bound s hs hs1 hz hdet f hf])

theorem optimizer_mem_closure (n : ℕ) :
    ZetaTwoOptimizerStage.optimizer n ∈ ZetaTwoOptimizerStage.closure := by
  apply (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_le
    ZetaTwoOptimizerStage.squarefreeAtom id n).trans
    (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).le_topologicalClosure
  exact (ZetaTwoOptimizerStage.stage n).starProjection_apply_mem qOne

theorem zero_optimizer_floor (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) (n : ℕ) :
    (2 * s.re - 1) / (zetaTwo * Complex.normSq s) ≤
      ZetaTwoOptimizerStage.error n :=
  zero_floor s hs hs1 hz _ (optimizer_mem_closure n)

theorem zero_limiting_floor (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) / (zetaTwo * Complex.normSq s) ≤
      ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2 :=
  zero_floor s hs hs1 hz _
    (ZetaTwoOptimizerStage.closure.starProjection_apply_mem qOne)

theorem zero_height_band (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) (f : QHilbert)
    (hf : f ∈ ZetaTwoOptimizerStage.closure) (T : ℝ) (hT : 0 ≤ T)
    (hheight : |s.im| ≤ T) :
    |s.re - 1 / 2| ≤ (zetaTwo / 2) * (1 + T ^ 2) * ‖qOne - f‖ ^ 2 := by
  have h := zero_horizontal_bound s hs0 hs1 hz f hf
  have hsq : s.im ^ 2 ≤ T ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s.im) hT).mpr hheight
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add_left hsq 1)
      (div_nonneg zetaTwo_pos.le (by norm_num : (0 : ℝ) ≤ 2)))
    (sq_nonneg ‖qOne - f‖)
  exact h.trans (by simpa only [add_comm] using hm)

theorem zero_free_rectangle_certificate (f : QHilbert)
    (hf : f ∈ ZetaTwoOptimizerStage.closure) (T ε : ℝ) (hT : 0 ≤ T)
    (hcert : (zetaTwo / 2) * (1 + T ^ 2) * ‖qOne - f‖ ^ 2 < ε) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
      |s.im| ≤ T → |s.re - 1 / 2| < ε := by
  intro s hs0 hs1 hz hheight
  exact lt_of_le_of_lt (zero_height_band s hs0 hs1 hz f hf T hT hheight) hcert

theorem zero_optimizer_height_band (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hheight : |s.im| ≤ T) :
    |s.re - 1 / 2| ≤ (zetaTwo / 2) * (1 + T ^ 2) * ZetaTwoOptimizerStage.error n :=
  zero_height_band s hs0 hs1 hz _ (optimizer_mem_closure n) T hT hheight

/-- The actual Q energy retains both the integral remainder and the full
positive correction from changing the law. No inverse is used. -/
theorem zeroGram_energy_exact {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hs1 : ∀ i, s i ≠ 1) (hz : ∀ i, riemannZeta (s i) = 0)
    (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    zetaTwo * ‖qOne - f‖ ^ 2 =
      2 * (∑ i, starRingEnd ℂ (c i) * (1 / s i)).re -
        (mellinGramQuadratic s c).re +
        (∫ x in Ioi (1 : ℝ),
          ‖mellinWeightedStep (toPareto (qOne - f)) x -
            starRingEnd ℂ (finiteMellinKernel s c x)‖ ^ 2) +
        zetaTwo * normCorrection (qOne - f) := by
  have h := finiteMellinKernel_remainder (toPareto (qOne - f)) s c hs
  simp_rw [residual_mellin_eq_one_div _ (hs _) (hs1 _) (hz _) f hf] at h
  rw [toPareto_norm_sq_exact] at h
  linarith

/-- Every finite zero-mode test gives a certificate, including singular and
redundant dictionaries. The law-change correction is retained. -/
theorem zeroGram_variational_bound {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hs1 : ∀ i, s i ≠ 1) (hz : ∀ i, riemannZeta (s i) = 0)
    (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    2 * (∑ i, starRingEnd ℂ (c i) * (1 / s i)).re -
        (mellinGramQuadratic s c).re +
        zetaTwo * normCorrection (qOne - f) ≤ zetaTwo * ‖qOne - f‖ ^ 2 := by
  have h := zeroGram_energy_exact s c hs hs1 hz f hf
  have hn : 0 ≤ ∫ x in Ioi (1 : ℝ),
      ‖mellinWeightedStep (toPareto (qOne - f)) x -
        starRingEnd ℂ (finiteMellinKernel s c x)‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

end RiemannResearch.RH.QZeroGramObstruction
