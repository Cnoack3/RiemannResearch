/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.ActualZetaSquareMellinShift
import RiemannResearch.Analysis.ActualZetaSquareFiniteHeadShift
import RiemannResearch.Analysis.WeightedDivisorMoment
import RiemannResearch.Analysis.ZetaSquareInfiniteTailKernel
import RiemannResearch.Analysis.ActualZetaFourthMomentDyadic
import Mathlib.Tactic.LinearCombination
/-!
# Exact remainder decomposition for the actual zeta square

The completed zeta functional equation holds on the entire reflected line,
including its real point. Absolute convergence of the divisor L-series
then splits the actual left Mellin kernel into its finite head and ordinary
infinite tail. Their integrability justifies the integral splitting.

Combining the actual zeta contour shift and the finite-head contour shift
expresses the existing residual as the smoothing defect minus the moving
residue, the right-head integral, and the left-tail integral. This identity
holds for every natural cutoff and every positive real smoothing scale.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis
open Zeta23.XiPrime Zeta23.XiPrime.Hardy

/-- Functional equation on the entire reflected line, including the real point. -/
theorem riemannZeta_eq_chiFE_mul_of_re_eq_neg_quarter {s : ℂ}
    (hs : s.re = -1 / 4) :
    riemannZeta s = chiFE s * riemannZeta (1 - s) := by
  have hs0 : s ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num [hs] at hr
  have hs1 : 1 - s ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num [hs] at hr
  have hG : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
    intro n hn
    have hr := congrArg Complex.re hn
    cases n with
    | zero => norm_num [hs] at hr
    | succ n =>
      norm_num [hs] at hr
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  have hG1 : Gammaℝ (1 - s) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
    intro n hn
    have hr := congrArg Complex.re hn
    norm_num [hs] at hr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1 := Zeta23.RvM.completedRiemannZeta_eq_Gammaℝ_mul hs0 hG
  have h2 := Zeta23.RvM.completedRiemannZeta_eq_Gammaℝ_mul hs1 hG1
  have hΛ := completedRiemannZeta_one_sub s
  rw [chiFE_def]
  field_simp
  rw [h1, h2] at *
  linear_combination -hΛ

private theorem tsum_eq_sum_Icc_add_tsum_gt {f : ℕ → ℂ}
    (hf : Summable f) (hf0 : f 0 = 0) (N : ℕ) :
    (∑' n : ℕ, f n) =
      (∑ n ∈ Finset.Icc 1 N, f n) + ∑' n : ℕ, if N < n then f n else 0 := by
  classical
  rw [← hf.sum_add_tsum_compl (s := Finset.Icc 1 N), tsum_subtype]
  congr 1
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [hf0]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp [Set.indicator, hn1, not_le]

/-- Exact ordinary-series splitting of the reflected zeta square at every height. -/
theorem reflectedZetaSquare_eq_head_add_tail (N : ℕ) (t v : ℝ) :
    riemannZeta (1 - ((1 / 2 : ℂ) + I * t +
      (((-3 / 4 : ℝ) : ℂ) + v * I))) ^ 2 =
      reflectedDivisorHead N t (((-3 / 4 : ℝ) : ℂ) + v * I) +
        fiveQuarterDivisorTail N (-(t + v)) := by
  have he : 1 - ((1 / 2 : ℂ) + I * t + (((-3 / 4 : ℝ) : ℂ) + v * I)) =
      (((1 / 2 - (-3 / 4) : ℝ) : ℂ) + I * (-(t + v) : ℝ)) := by
    push_cast
    ring
  rw [he, riemannZeta_sq_eq_divisorLSeries (by norm_num)]
  change (∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.sigma 0 n : ℂ))
    (((1 / 2 - (-3 / 4) : ℝ) : ℂ) + I * (-(t + v) : ℝ)) n) = _
  simp_rw [← powerWeightedDivisorTerm_eq_LSeries_term (-3 / 4) (-(t + v))]
  rw [tsum_eq_sum_Icc_add_tsum_gt (summable_fiveQuarterDivisorTerm (-(t + v)))
    (by simp [powerWeightedDivisorTerm, criticalDivisorCoefficient]) N]
  rw [reflectedDivisorHead_vertical]
  rfl

/-- The actual left kernel is pointwise the finite head plus the infinite tail. -/
theorem zetaSquareMellinKernel_left_eq_head_add_tail (N : ℕ) (Y t v : ℝ) :
    zetaSquareMellinKernel Y t (((-3 / 4 : ℝ) : ℂ) + v * I) =
      zetaSquareFiniteHeadKernel N Y t (((-3 / 4 : ℝ) : ℂ) + v * I) +
        zetaSquareInfiniteTailKernel N Y t v := by
  rw [zetaSquareMellinKernel,
    riemannZeta_eq_chiFE_mul_of_re_eq_neg_quarter (by norm_num), mul_pow,
    reflectedZetaSquare_eq_head_add_tail N t v]
  unfold zetaSquareFiniteHeadKernel zetaSquareInfiniteTailKernel
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

/-- Absolute vertical integrability follows from the full and finite-head kernels. -/
theorem integrable_zetaSquareInfiniteTailKernel (N : ℕ) {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) :
    Integrable (zetaSquareInfiniteTailKernel N Y t) := by
  have he : zetaSquareInfiniteTailKernel N Y t =
      fun v : ℝ => zetaSquareMellinKernel Y t (((-3 / 4 : ℝ) : ℂ) + v * I) -
        zetaSquareFiniteHeadKernel N Y t (((-3 / 4 : ℝ) : ℂ) + v * I) := by
    funext v
    rw [zetaSquareMellinKernel_left_eq_head_add_tail]
    ring
  rw [he]
  exact (integrable_zetaSquareMellinKernel_negative hY t (by norm_num) (by norm_num)).sub
    (integrable_zetaSquareFiniteHeadKernel_vertical N hY t
      (by norm_num) (by norm_num) (by norm_num))

/-- Exact consumer form of the actual residual, with both contour signs retained. -/
theorem zetaSquareResidual_eq_mellin_remainder (N : ℕ) {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) :
    zetaSquareResidual (divisorPolynomial N (fun _ => 1))
      (fun u => zetaSquareCriticalPhase u * star (divisorPolynomial N (fun _ => 1) u)) t =
      (dampedDivisorSeries Y t - divisorPolynomial N (fun _ => 1) t) -
        zetaSquareMovingResidue Y t -
        (1 / (2 * (Real.pi : ℂ))) *
          (∫ v : ℝ, zetaSquareFiniteHeadKernel N Y t ((b : ℂ) + v * I)) -
        zetaSquareInfiniteTailIntegral N Y t := by
  have hshift := zetaSquareMellinIntegral_eq_residues_add_leftIntegral hY t
    (a := -3 / 4) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  have hinv := dampedDivisorSeries_eq_mellinIntegral hY t (c := 1) (by norm_num)
  have hs : dampedDivisorSeries Y t =
      riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2 + zetaSquareMovingResidue Y t +
        (1 / (2 * (Real.pi : ℂ))) *
          (∫ v : ℝ, zetaSquareMellinKernel Y t (((-3 / 4 : ℝ) : ℂ) + v * I)) := by
    rw [hinv]
    simpa only [mul_comm I] using hshift
  have hh' := zetaSquareFiniteHeadIntegral_eq_residue_add_leftIntegral N hY t
    (a := -3 / 4) (b := b) (by norm_num) (by norm_num) hb hb'
  have hi :
      (∫ v : ℝ, zetaSquareMellinKernel Y t (((-3 / 4 : ℝ) : ℂ) + v * I)) =
        (∫ v : ℝ, zetaSquareFiniteHeadKernel N Y t (((-3 / 4 : ℝ) : ℂ) + v * I)) +
          ∫ v : ℝ, zetaSquareInfiniteTailKernel N Y t v := by
    simp_rw [zetaSquareMellinKernel_left_eq_head_add_tail N Y t]
    exact integral_add
      (integrable_zetaSquareFiniteHeadKernel_vertical N hY t
        (by norm_num) (by norm_num) (by norm_num))
      (integrable_zetaSquareInfiniteTailKernel N hY t)
  rw [hi, mul_add] at hs
  simp only [zetaSquareResidual, zetaSquareCriticalPhase, zetaSquareInfiniteTailIntegral,
    Complex.star_def]
  linear_combination -hs + hh'

end RiemannResearch.Analysis
