/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteTwistedMoment
import RiemannResearch.Analysis.MarkedFourierTail
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
/-!
# Exact finite Gaussian means and interval majorants

Source: the user's Ingham/Z03 continuation, obligation I2, motivates this
mean-value input. The proof uses Mathlib's Gaussian characteristic function
and the existing weighted symmetric-kernel inequality. It retains the full
signed double sum before taking its norm. No arithmetic hypothesis occurs
in the identity; the upper estimate exposes its Gaussian row bound.

The actual Dirichlet-polynomial application discharges that row bound in
`DirichletPolynomialMeanValue.lean`.
-/

noncomputable section
open MeasureTheory Complex ProbabilityTheory Set
open scoped BigOperators NNReal

namespace Complex
theorem integrable_exp_phase_gaussian (w : ℝ) (v : ℝ≥0) :
    Integrable (fun t : ℝ => exp (I * t * w)) (gaussianReal 0 v) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (show AEStronglyMeasurable (fun t : ℝ => exp (I * t * w)) (gaussianReal 0 v)
      from (by fun_prop : Continuous (fun t : ℝ => exp (I * t * w))).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun t => by rw [norm_exp]; simp)

theorem integral_exp_phase_gaussian (w : ℝ) (v : ℝ≥0) :
    (∫ t : ℝ, exp (I * t * w) ∂gaussianReal 0 v) =
      (Real.exp (-(v : ℝ) * w ^ 2 / 2) : ℂ) := by
  calc
    _ = charFun (gaussianReal 0 v) w := by
      rw [charFun_apply_real]
      congr 1
      funext t
      congr 1
      ring
    _ = _ := by
      rw [charFun_gaussianReal, Complex.ofReal_exp]
      congr 1
      push_cast
      ring

theorem integral_exp_sum_gaussian_identity {ι : Type* } (S : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (v : ℝ≥0) :
    ((∫ t : ℝ, ‖∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2
      ∂gaussianReal 0 v : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, a m * star (a n) *
        (Real.exp (-(v : ℝ) * (ω m - ω n) ^ 2 / 2) : ℂ) := by
  have he (t : ℝ) :
      (‖∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2 : ℝ) =
        ∑ m ∈ S, ∑ n ∈ S, a m * star (a n) * exp (I * t * (ω m - ω n)) := by
    simpa using finite_sum_norm_sq_expansion S a ω 1 t
  rw [← integral_complex_ofReal]
  simp_rw [he]
  have hi (m n : ι) : Integrable
      (fun t : ℝ => a m * star (a n) * exp (I * t * (ω m - ω n))) (gaussianReal 0 v) :=
    by
      simpa only [Complex.ofReal_sub] using
        (integrable_exp_phase_gaussian (ω m - ω n) v).const_mul (a m * star (a n))
  rw [integral_finsetSum S (fun m _ => integrable_finsetSum S (fun n _ => hi m n))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finsetSum S (fun n _ => hi m n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_const_mul, ← Complex.ofReal_sub, integral_exp_phase_gaussian]

theorem integral_exp_sum_gaussian_le {ι : Type* } (S : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (v : ℝ≥0) (D : ℝ)
    (hrow : ∀ m ∈ S, ∑ n ∈ S,
      Real.exp (-(v : ℝ) * (ω m - ω n) ^ 2 / 2) ≤ D) :
    (∫ t : ℝ, ‖∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2 ∂gaussianReal 0 v) ≤
      D * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have he := congrArg norm (integral_exp_sum_gaussian_identity S a ω v)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))] at he
  rw [he]
  calc
    _ ≤ ∑ m ∈ S, ∑ n ∈ S, ‖a m * star (a n) *
        (Real.exp (-(v : ℝ) * (ω m - ω n) ^ 2 / 2) : ℂ)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => norm_sum_le _ _))
    _ = ∑ m ∈ S, ∑ n ∈ S,
        Real.exp (-(v : ℝ) * (ω m - ω n) ^ 2 / 2) * ‖a m‖ * ‖a n‖ := by
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ _ := RiemannResearch.Analysis.MarkedFourierTail.symmetric_kernel_quadratic_le_row_bound
      S (fun n => ‖a n‖) (fun m n => Real.exp (-(v : ℝ) * (ω m - ω n) ^ 2 / 2)) D
      (fun m _ n _ => Real.exp_nonneg _)
      (fun m _ n _ => by congr 1; ring) hrow

theorem exp_sum_norm_le {ι : Type* } (S : Finset ι) (a : ι → ℂ) (ω : ι → ℝ) (t : ℝ) :
    ‖∑ n ∈ S, a n * exp (I * t * ω n)‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro n hn
  rw [norm_mul, norm_exp]
  simp

theorem integrable_gaussianPDF_exp_sum_sq {ι : Type* } (S : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun t : ℝ => gaussianPDFReal 0 v t *
      ‖∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2) := by
  refine Integrable.mono'
    ((integrable_gaussianPDFReal 0 v).mul_const ((∑ n ∈ S, ‖a n‖) ^ 2))
    (show AEStronglyMeasurable (fun t : ℝ => gaussianPDFReal 0 v t *
      ‖∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2) volume from (by
        unfold gaussianPDFReal
        fun_prop : Continuous (fun t : ℝ => gaussianPDFReal 0 v t *
          ‖∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2)).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (exp_sum_norm_le S a ω t) 2)
      (gaussianPDFReal_nonneg _ _ _))

theorem gaussianPDF_scale_floor {L t : ℝ} (hL : 0 < L) (ht : |t| ≤ L) :
    Real.exp (-(1 / 2 : ℝ)) / (Real.sqrt (2 * Real.pi) * L) ≤
      gaussianPDFReal 0 ⟨L ^ 2, sq_nonneg L⟩ t := by
  have hsq : t ^ 2 ≤ L ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  change Real.exp (-(1 / 2 : ℝ)) / (Real.sqrt (2 * Real.pi) * L) ≤
    (Real.sqrt (2 * Real.pi * L ^ 2))⁻¹ * Real.exp (-(t - 0) ^ 2 / (2 * L ^ 2))
  simp only [sub_zero]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), Real.sqrt_sq hL.le]
  rw [div_eq_mul_inv, mul_comm (Real.exp _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ (by positivity : 0 < 2 * L ^ 2)).mpr
  nlinarith

theorem integral_exp_sum_le_of_gaussian_rows {ι : Type* } (S : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) {T L D : ℝ} (hT : 0 ≤ T) (hL : 0 < L) (hTL : T ≤ L)
    (hrow : ∀ m ∈ S, ∑ n ∈ S, Real.exp (-L ^ 2 * (ω m - ω n) ^ 2 / 2) ≤ D) :
    (∫ t in (0 : ℝ)..T, ‖∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2) ≤
      (D * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * L *
        ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let v : ℝ≥0 := ⟨L ^ 2, sq_nonneg L⟩
  let F : ℝ → ℝ := fun t => ‖∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2
  let c : ℝ := Real.exp (-(1 / 2 : ℝ)) / (Real.sqrt (2 * Real.pi) * L)
  have hc : 0 < c := by dsimp [c]; positivity
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hi := integrable_gaussianPDF_exp_sum_sq S a ω v
  have hb : c * (∫ t in (0 : ℝ)..T, F t) ≤ D * ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hT, ← integral_const_mul]
    calc
      _ ≤ ∫ t in Ioc (0 : ℝ) T, gaussianPDFReal 0 v t * F t := by
        apply integral_mono_ae
          ((hF.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul _) hi.restrict
        exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact gaussianPDF_scale_floor hL (by rw [abs_of_pos ht.1]; exact ht.2.trans hTL))
      _ ≤ ∫ t, gaussianPDFReal 0 v t * F t :=
        setIntegral_le_integral hi (Filter.Eventually.of_forall (fun t =>
          mul_nonneg (gaussianPDFReal_nonneg _ _ _) (sq_nonneg _)))
      _ = ∫ t, F t ∂gaussianReal 0 v := by
        rw [integral_gaussianReal_eq_integral_smul (show v ≠ 0 by
          have hv : (0 : ℝ) < v := by change 0 < L ^ 2; positivity
          exact_mod_cast hv.ne')]
        rfl
      _ ≤ _ := integral_exp_sum_gaussian_le S a ω v D hrow
  have he : c * ((D * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * L *
      ∑ n ∈ S, ‖a n‖ ^ 2) = D * ∑ n ∈ S, ‖a n‖ ^ 2 := by
    dsimp [c]
    have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    have hx : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2 : ℝ) = 1 := by
      rw [← Real.exp_add]; norm_num
    calc
      _ = (Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2 : ℝ)) * D *
          ∑ n ∈ S, ‖a n‖ ^ 2 := by field_simp
      _ = _ := by rw [hx]; ring
  exact (mul_le_mul_iff_right₀ hc).mp (hb.trans_eq he.symm)
end Complex
