/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import RiemannResearch.Analysis.ActualZetaSquareFiniteHeadShift
import RiemannResearch.Analysis.WeightedDivisorMoment
import RiemannResearch.Analysis.WeightedIntegralMeanSquare
import RiemannResearch.Analysis.MellinGammaEnvelope
import RiemannResearch.Analysis.ZetaSquareMellinWeights
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

/-!
# Uniform second moment of the actual right-hand Mellin head

The whole vertical contour is controlled by the integrable quadratic Gamma
envelope. The chi factor is bounded at every translated height, including
the real-axis crossing. Weighted divisor moments then give a bound uniform
in every positive smoothing scale and every cutoff at most the dyadic height.

Source for the contour organization: Chourasiya--Simonic, Section 5.1,
https://arxiv.org/html/2507.15184v2. The mean-square transfer uses the proved
weighted Cauchy--Schwarz/Fubini lemma and the actual divisor polynomial.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
open scoped ComplexConjugate
namespace RiemannResearch.Analysis

/-- The normalized full right-hand contour integral of the actual finite head. -/
def zetaSquareRightHeadIntegral (N : ℕ) (Y t : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ v : ℝ, zetaSquareFiniteHeadKernel N Y t ((1 / 4 : ℂ) + v * I)

/-- Uniform all-scale right-head estimate. Neither the smoothing scale nor the
cutoff needs to be comparable from below to the dyadic height. -/
theorem exists_zetaSquareRightHeadIntegral_uniform_second_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (Y U : ℝ),
      0 < N → 0 < Y → Y ≤ U → 1 ≤ U → (N : ℝ) ≤ U →
      IntervalIntegrable (zetaSquareRightHeadIntegral N Y) volume U (2 * U) ∧
      IntervalIntegrable (fun t => ‖zetaSquareRightHeadIntegral N Y t‖ ^ 2)
        volume U (2 * U) ∧
      (∫ t in U..2 * U, ‖zetaSquareRightHeadIntegral N Y t‖ ^ 2) ≤
        C * U * (1 + Real.log N) ^ 4 := by
  obtain ⟨C, hC, hχ⟩ :=
    SymmetricZetaRatio.exists_chiFE_three_quarters_square_translated_bound
  let c : ℂ := 1 / (2 * (Real.pi : ℂ))
  let w : ℝ → ℝ := fun v => ‖Gamma ((1 / 4 : ℂ) + v * I)‖ * (1 + |v|) ^ 2
  let W : ℝ := ∫ v : ℝ, w v
  let B : ℝ := ‖c‖ * C
  have hK : 0 ≤ divisorMeanValueConstant := by
    unfold divisorMeanValueConstant
    positivity
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg _) hC
  have hw : Continuous w := by
    have hg := continuous_Gamma_vertical_of_neg_one_lt (a := 1 / 4)
      (by norm_num) (by norm_num)
    norm_num at hg
    exact hg.norm.mul (show Continuous (fun v : ℝ => (1 + |v|) ^ 2) from by fun_prop)
  have hwi : Integrable w := by
    simpa only [w, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      integrable_Gamma_vertical_quadratic_weight
        (a := 1 / 4) (by norm_num) (by norm_num)
  have hw0 (v : ℝ) : 0 ≤ w v := by dsimp [w]; positivity
  refine ⟨2 * divisorMeanValueConstant * (B * W) ^ 2, by positivity, ?_⟩
  intro N Y U hN hY hYU hU hNU
  have hU0 : 0 < U := by linarith
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hUT : U ≤ 2 * U := by linarith
  let F : ℝ × ℝ → ℂ := fun p => conj (quarterDivisorHead N (p.1 + p.2))
  let G : ℝ × ℝ → ℂ := fun p =>
    c * zetaSquareFiniteHeadKernel N Y p.1 ((1 / 4 : ℂ) + p.2 * I)
  let k : ℝ → ℝ := fun v => (B * U ^ (-1 / 4 : ℝ)) * w v
  have hk : Continuous k := continuous_const.mul hw
  have hki : Integrable k := hwi.const_mul _
  have hk0 (v : ℝ) : 0 ≤ k v := by dsimp [k]; positivity
  have hF : Continuous F :=
    Complex.continuous_conj.comp ((continuous_quarterDivisorHead N).comp
      (continuous_fst.add continuous_snd))
  have hG : Continuous G := by
    have hh := continuous_zetaSquareFiniteHeadKernel_vertical_joint N hY
      (r := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
    simpa only [G, Pi.mul_apply, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using!
      (show Continuous (fun _ : ℝ × ℝ => c) from continuous_const).mul hh
  obtain ⟨D, hD, hDb⟩ := quarterDivisorHead_uniform_bound N
  have hFb (p : ℝ × ℝ) : ‖F p‖ ≤ D := by
    simpa only [F, norm_conj] using hDb (p.1 + p.2)
  have hscale : U ^ (1 / 4 : ℝ) * U ^ (-1 / 2 : ℝ) = U ^ (-1 / 4 : ℝ) := by
    rw [← Real.rpow_add hU0]
    norm_num
  have hGb : ∀ t ∈ Icc U (2 * U), ∀ v : ℝ, ‖G (t, v)‖ ≤ k v * ‖F (t, v)‖ := by
    intro t ht v
    have hzeta : (1 / 2 : ℂ) + I * t + ((1 / 4 : ℂ) + v * I) =
        (3 / 4 : ℂ) + I * ((t + v : ℝ) : ℂ) := by push_cast; ring
    have hhead : reflectedDivisorHead N t ((1 / 4 : ℂ) + v * I) =
        conj (quarterDivisorHead N (t + v)) := by
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
        quarterDivisorHead] using reflectedDivisorHead_vertical_eq_conj N (1 / 4) t v
    have hpow : ‖(Y : ℂ) ^ ((1 / 4 : ℂ) + v * I)‖ = Y ^ (1 / 4 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      congr 1
      norm_num
    have hy : Y ^ (1 / 4 : ℝ) ≤ U ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hY.le hYU (by norm_num)
    have hn : ‖G (t, v)‖ =
        ‖c‖ * (‖Gamma ((1 / 4 : ℂ) + v * I)‖ * Y ^ (1 / 4 : ℝ) *
          ‖Zeta23.XiPrime.chiFE ((3 / 4 : ℂ) + I * ((t + v : ℝ) : ℂ)) ^ 2‖ *
            ‖F (t, v)‖) := by
      dsimp only [G]
      rw [norm_mul, zetaSquareFiniteHeadKernel, norm_mul, norm_mul, norm_mul,
        hpow, hzeta, hhead]
    rw [hn]
    calc
      _ ≤ ‖c‖ * (‖Gamma ((1 / 4 : ℂ) + v * I)‖ * U ^ (1 / 4 : ℝ) *
          (C * U ^ (-1 / 2 : ℝ) * (1 + |v|) ^ 2) * ‖F (t, v)‖) := by
        gcongr
        exact hχ U t v hU ht.1
      _ = k v * ‖F (t, v)‖ := by
        dsimp [k, w, B]
        calc
          _ = (‖c‖ * C) * (U ^ (1 / 4 : ℝ) * U ^ (-1 / 2 : ℝ)) *
              (‖Gamma ((1 / 4 : ℂ) + v * I)‖ * (1 + |v|) ^ 2) *
                ‖F (t, v)‖ := by ring
          _ = _ := by rw [hscale]
  have hM (v : ℝ) :
      (∫ t in U..2 * U, ‖F (t, v)‖ ^ 2) ≤
        2 * divisorMeanValueConstant * U ^ (3 / 2 : ℝ) * (1 + Real.log N) ^ 4 := by
    simp only [F, norm_conj]
    rw [intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => ‖quarterDivisorHead N x‖ ^ 2)]
    have hh := quarterDivisorHead_second_moment_le hN
      (H := U + v) (T := 2 * U + v) (by linarith)
    have hpowU : U * U ^ (1 / 2 : ℝ) = U ^ (3 / 2 : ℝ) := by
      calc
        _ = U ^ (1 : ℝ) * U ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
        _ = U ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hU0 _ _).symm
        _ = _ := by norm_num
    calc
      _ ≤ divisorMeanValueConstant * ((2 * U + v) - (U + v) + N) *
          ((N : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log N) ^ 4) := hh
      _ ≤ divisorMeanValueConstant * (2 * U) *
          (U ^ (1 / 2 : ℝ) * (1 + Real.log N) ^ 4) := by
        gcongr
        linarith
      _ = _ := by
        calc
          _ = 2 * divisorMeanValueConstant * (U * U ^ (1 / 2 : ℝ)) *
              (1 + Real.log N) ^ 4 := by ring
          _ = _ := by rw [hpowU]
  have hi := MeasureTheory.intervalIntegrable_integral_and_norm_sq_of_weighted_bound
    hki hG hUT (D := D) (fun t ht v =>
      (hGb t ht v).trans (mul_le_mul_of_nonneg_left (hFb (t, v)) (hk0 v)))
  have hmain := MeasureTheory.interval_integral_norm_integral_sq_le_weighted
    hk hki hk0 hF hG hUT hFb hGb hM
  have he (t : ℝ) : (∫ v : ℝ, G (t, v)) = zetaSquareRightHeadIntegral N Y t := by
    dsimp [G, zetaSquareRightHeadIntegral, c]
    rw [MeasureTheory.integral_const_mul]
  simp_rw [he] at hi hmain
  refine ⟨hi.1, hi.2, hmain.trans ?_⟩
  have hkint : (∫ v : ℝ, k v) = (B * U ^ (-1 / 4 : ℝ)) * W :=
    MeasureTheory.integral_const_mul _ w
  rw [hkint]
  have hp : (U ^ (-1 / 4 : ℝ)) ^ 2 * U ^ (3 / 2 : ℝ) = U := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le, ← Real.rpow_add hU0]
    norm_num
  apply le_of_eq
  calc
    _ = (2 * divisorMeanValueConstant * (B * W) ^ 2) *
        ((U ^ (-1 / 4 : ℝ)) ^ 2 * U ^ (3 / 2 : ℝ)) * (1 + Real.log N) ^ 4 := by ring
    _ = _ := by rw [hp]

/-- The canonical choice Y=N, retaining only the upper cutoff restriction. -/
theorem exists_zetaSquareFiniteHeadIntegral_dyadic_second_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (U : ℝ), 0 < N → 1 ≤ U → (N : ℝ) ≤ U →
      IntervalIntegrable (fun t => ‖(1 / (2 * (Real.pi : ℂ))) *
        (∫ v : ℝ, zetaSquareFiniteHeadKernel N N t ((1 / 4 : ℂ) + v * I))‖ ^ 2)
          volume U (2 * U) ∧
      (∫ t in U..2 * U, ‖(1 / (2 * (Real.pi : ℂ))) *
        (∫ v : ℝ, zetaSquareFiniteHeadKernel N N t ((1 / 4 : ℂ) + v * I))‖ ^ 2) ≤
          C * U * (1 + Real.log N) ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := exists_zetaSquareRightHeadIntegral_uniform_second_moment
  refine ⟨C, hC, ?_⟩
  intro N U hN hU hNU
  obtain ⟨_, hi, hb⟩ := hbound N N U hN (by exact_mod_cast hN) hNU hU hNU
  exact ⟨hi, hb⟩

end RiemannResearch.Analysis
