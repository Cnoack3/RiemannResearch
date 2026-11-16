/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import RiemannResearch.Analysis.ZetaSquareInfiniteTailKernel
import RiemannResearch.Analysis.WeightedIntegralMeanSquare
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform square moment of the actual infinite-tail Mellin integral

The full real-line chi weight and a quadratic Gamma envelope transfer the
translated five-quarter divisor-tail moment by weighted Cauchy--Schwarz
and Fubini. No central/far truncation is used. The cutoff only needs
U <= 2N; it need not be bounded above by U.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
namespace RiemannResearch.Analysis

private theorem tail_mellin_scale_le {U n : ℝ} (hU : 0 ≤ U) (hn : 0 < n)
    (hUn : U ≤ 2*n) :
    (U ^ (3/2 : ℝ) * n ^ (-3/4 : ℝ)) ^ 2 * n ^ (-1/2 : ℝ) ≤ 4*U := by
  have hu : (U ^ (3/2 : ℝ)) ^ 2 = U ^ 3 := by
    rw [← Real.rpow_natCast (U ^ (3/2 : ℝ)) 2, ← Real.rpow_mul hU]
    norm_num
  have hn' : (n ^ (-3/4 : ℝ)) ^ 2 * n ^ (-1/2 : ℝ) = (n ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast (n ^ (-3/4 : ℝ)) 2, ← Real.rpow_mul hn.le]
    norm_num
    rw [← Real.rpow_add hn]
    norm_num
  rw [mul_pow, hu, mul_assoc, hn', ← div_eq_mul_inv]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  have hs := pow_le_pow_left₀ hU hUn 2
  have hm := mul_le_mul_of_nonneg_left hs hU
  nlinarith

/-- The actual normalized left-tail Mellin integral has the required uniform
dyadic second moment. The only cutoff restriction is U <= 2N. -/
theorem exists_zetaSquareInfiniteTailIntegral_dyadic_second_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ U : ℝ, 2 ≤ U → U ≤ 2*N →
      IntervalIntegrable (fun t => ‖zetaSquareInfiniteTailIntegral N N t‖ ^ 2)
        volume U (2*U) ∧
      (∫ t in U..2*U, ‖zetaSquareInfiniteTailIntegral N N t‖ ^ 2) ≤
        C * U * (1 + Real.log N) ^ 4 := by
  obtain ⟨Cχ, hCχ, hχ⟩ :=
    SymmetricZetaRatio.exists_chiFE_neg_quarter_square_translated_bound
  let g : ℝ → ℝ := fun v => ‖Gamma ((-3/4 : ℂ) + v*I)‖ * (1+|v|)^2
  let J : ℝ := ∫ v : ℝ, g v
  let B : ℝ := 18 * fiveQuarterDivisorMomentConstant
  let q : ℂ := 1 / (2 * (Real.pi : ℂ))
  have hB : 0 ≤ B := mul_nonneg (by norm_num) fiveQuarterDivisorMomentConstant_nonneg
  have hg : Continuous g := by
    have hh : Continuous (fun v : ℝ => Gamma ((-3/4 : ℂ) + v*I)) := by
      convert continuous_Gamma_vertical_of_neg_one_lt
        (a := -3/4) (by norm_num) (by norm_num) using 1 <;> norm_num
    exact hh.norm.mul (by fun_prop)
  have hgi : Integrable g := by
    simpa only [g, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
      integrable_Gamma_vertical_quadratic_weight
        (a := -3/4) (by norm_num) (by norm_num)
  have hg0 : ∀ v, 0 ≤ g v := fun v => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  refine ⟨4 * ‖q‖^2 * (Cχ * J)^2 * B, by positivity, ?_⟩
  intro N hN U hU hUN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hU0 : 0 ≤ U := by linarith
  let A : ℝ := Cχ * U ^ (3/2 : ℝ) * (N : ℝ) ^ (-3/4 : ℝ)
  let k : ℝ → ℝ := fun v => A * g v
  let F : ℝ × ℝ → ℂ := fun p => fiveQuarterDivisorTail N (-(p.1+p.2))
  let G : ℝ × ℝ → ℂ := fun p => zetaSquareInfiniteTailKernel N N p.1 p.2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hk : Continuous k := hg.const_mul A
  have hki : Integrable k := hgi.const_mul A
  have hk0 : ∀ v, 0 ≤ k v := fun v => mul_nonneg hA (hg0 v)
  have hF : Continuous F :=
    (continuous_fiveQuarterDivisorTail hN).comp (continuous_fst.add continuous_snd).neg
  have hG : Continuous G := continuous_zetaSquareInfiniteTailKernel_joint N hN0
  obtain ⟨D, _, hD⟩ := fiveQuarterDivisorTail_uniform_bound hN
  have hFD : ∀ p, ‖F p‖ ≤ D := fun p => hD _
  have hGb : ∀ t ∈ Icc U (2*U), ∀ v, ‖G (t,v)‖ ≤ k v * ‖F (t,v)‖ := by
    intro t ht v
    have hy : ‖((N : ℝ) : ℂ) ^ ((-3/4 : ℂ) + v*I)‖ =
        (N : ℝ) ^ (-3/4 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0]
      norm_num
    have he : (1/2 : ℂ) + I*t + ((-3/4 : ℂ) + v*I) =
        (-1/4 : ℂ) + I*((t+v : ℝ) : ℂ) := by push_cast; ring
    have hc := hχ U t v (by linarith) ht
    change ‖zetaSquareInfiniteTailKernel N N t v‖ ≤ _
    rw [zetaSquareInfiniteTailKernel, norm_mul, norm_mul, norm_mul, hy, he]
    calc
      _ ≤ (‖Gamma ((-3/4 : ℂ) + v*I)‖ * (N : ℝ)^(-3/4 : ℝ)) *
          (Cχ * U^(3/2 : ℝ) * (1+|v|)^2) * ‖fiveQuarterDivisorTail N (-(t+v))‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc (by positivity)) (norm_nonneg _)
      _ = k v * ‖F (t,v)‖ := by dsimp [k, A, g, F]; ring
  have hM (v : ℝ) : (∫ t in U..2*U, ‖F (t,v)‖ ^ 2) ≤
      B * (N : ℝ)^(-1/2 : ℝ) * (1+Real.log N)^4 := by
    have he (t : ℝ) : -(t+v) = -v-t := by ring
    dsimp only [F]
    simp_rw [he]
    rw [intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => ‖fiveQuarterDivisorTail N x‖ ^ 2) (-v)]
    exact fiveQuarterDivisorTail_second_moment_le_short hN
      (by linarith) (by linarith)
  have hGbD : ∀ t ∈ Icc U (2*U), ∀ v, ‖G (t,v)‖ ≤ k v * D := by
    intro t ht v
    exact (hGb t ht v).trans (mul_le_mul_of_nonneg_left (hFD (t,v)) (hk0 v))
  have hi := MeasureTheory.intervalIntegrable_integral_and_norm_sq_of_weighted_bound
    hki hG (by linarith : U ≤ 2*U) hGbD
  have hb := MeasureTheory.interval_integral_norm_integral_sq_le_weighted
    hk hki hk0 hF hG (by linarith : U ≤ 2*U) hFD hGb hM
  have hkint : (∫ v : ℝ, k v) = A*J := by
    exact integral_const_mul A g
  rw [hkint] at hb
  have hs := tail_mellin_scale_le hU0 hN0 hUN
  constructor
  · simpa only [zetaSquareInfiniteTailIntegral, norm_mul, mul_pow, G, q] using
      hi.2.const_mul (‖q‖^2)
  · calc
      _ = ‖q‖^2 * (∫ t in U..2*U, ‖∫ v : ℝ, G (t,v)‖^2) := by
        simp only [zetaSquareInfiniteTailIntegral, norm_mul, mul_pow, G, q,
          intervalIntegral.integral_const_mul]
      _ ≤ ‖q‖^2 * ((A*J)^2 *
          (B * (N : ℝ)^(-1/2 : ℝ) * (1+Real.log N)^4)) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = (‖q‖^2 * (Cχ*J)^2 * B) *
          ((U^(3/2 : ℝ) * (N : ℝ)^(-3/4 : ℝ))^2 * (N : ℝ)^(-1/2 : ℝ)) *
            (1+Real.log N)^4 := by dsimp [A]; ring
      _ ≤ (‖q‖^2 * (Cχ*J)^2 * B) * (4*U) * (1+Real.log N)^4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (4 * ‖q‖^2 * (Cχ * J)^2 * B) * U * (1+Real.log N)^4 := by ring

end RiemannResearch.Analysis
