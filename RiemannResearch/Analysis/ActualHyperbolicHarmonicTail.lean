/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualHyperbolicTailFrames
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import RiemannResearch.Analysis.ActualZeroCriticalLineTailFraction
import RiemannResearch.Analysis.FiniteHyperbolicHarmonicCap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Harmonic bounds for the actual signed hyperbolic tail

Every actual zero copy, both exponential channels, the strict bad mask,
and the original full Ncount normalization are retained. The harmonic cap
controls the signed quadratic form and the complete operator norm. The
masked good operator has an explicit full-minus-bad norm bound.

Source: the finite cap calculation in RH/ActualHyperbolicLowerBounds20261005.md.
The constant-proportion corollaries use the imported cumulative
Alpöge--Furman theorem (arXiv:2608.13637v2, Appendix A):
https://arxiv.org/html/2608.13637v2 . The proportion supplies no exponential
decay for a shrinking mask; the displacement-sensitive analytic density
provider remains a separate formalization obligation.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroOrdinate CenteredHyperbolicFrames
open FiniteHyperbolicHarmonicCap ContinuousLinearMap

theorem actualPhaseRow_norm (T : ℝ) (d : ℕ) (c : Copies T) (n : Fin d) :
    ‖actualPhaseRow T d c n‖ = (Real.sqrt (Ncount 0 T : ℝ))⁻¹ := by
  unfold actualPhaseRow
  rw [norm_mul, norm_star, copyPhaseVector_apply, phase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem actualExponentialVector_norm_sq (T : ℝ) (d : ℕ)
    (c : Copies T) (r : ℝ) :
    ‖actualExponentialVector T d c r‖^2 =
      (Ncount 0 T : ℝ)⁻¹*
        finiteExponentialSum (centeredFrequency d) (2*r*actualShift T c) := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold finiteExponentialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  change ‖(Real.exp (r*actualShift T c*centeredFrequency d n) : ℂ)*
    star (actualPhaseRow T d c n)‖^2 = _
  rw [norm_mul, norm_star, actualPhaseRow_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [pow_two, ← Real.exp_add]
  rw [show r*actualShift T c*centeredFrequency d n+
      r*actualShift T c*centeredFrequency d n =
      (2*r*actualShift T c)*centeredFrequency d n by ring]
  ring

theorem actualExponentialVector_cross_re (T : ℝ) (d : ℕ) (c : Copies T) :
    (inner ℂ (actualExponentialVector T d c 1)
      (actualExponentialVector T d c (-1))).re =
        (Ncount 0 T : ℝ)⁻¹*(d : ℝ) := by
  rw [PiLp.inner_apply, Complex.re_sum]
  have hcoord (n : Fin d) :
      (actualExponentialVector T d c (-1) n*
        star (actualExponentialVector T d c 1 n)).re = (Ncount 0 T : ℝ)⁻¹ := by
    have hp := actualPhaseRow_product T d c n n
    have hp' : actualPhaseRow T d c n*star (actualPhaseRow T d c n) =
        (Ncount 0 T : ℂ)⁻¹ := by
      simpa [frequencyGap, phase] using hp
    have he : Real.exp (-actualShift T c*centeredFrequency d n)*
        Real.exp (actualShift T c*centeredFrequency d n) = 1 := by
      rw [← Real.exp_add]
      simp
    change (((Real.exp (-1*actualShift T c*centeredFrequency d n) : ℂ)*
      star (actualPhaseRow T d c n))*star
      ((Real.exp (1*actualShift T c*centeredFrequency d n) : ℂ)*
        star (actualPhaseRow T d c n))).re = _
    simp only [one_mul, neg_one_mul, star_mul,
      Complex.star_def, Complex.conj_ofReal]
    have h : ((Real.exp (-actualShift T c*centeredFrequency d n) : ℂ)*
      star (actualPhaseRow T d c n))*
      ((Real.exp (actualShift T c*centeredFrequency d n) : ℂ)*
        actualPhaseRow T d c n) = (Ncount 0 T : ℂ)⁻¹ := by
      calc
        _ = ((Real.exp (-actualShift T c*centeredFrequency d n)*
          Real.exp (actualShift T c*centeredFrequency d n) : ℝ) : ℂ)*
          (actualPhaseRow T d c n*star (actualPhaseRow T d c n)) := by
            push_cast
            ring
        _ = _ := by rw [he, Complex.ofReal_one, one_mul, hp']
    simpa [mul_comm, add_comm] using congrArg Complex.re h
  change (∑ n : Fin d,
    (actualExponentialVector T d c (-1) n*
      star (actualExponentialVector T d c 1 n)).re) = _
  simp_rw [hcoord]
  simp only [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem actualHyperbolicCopyCap_le_harmonic (T : ℝ) (d : ℕ) (c : Copies T) :
    actualHyperbolicCopyCap T d c ≤
      (Ncount 0 T : ℝ)⁻¹*harmonicHyperbolicCap d := by
  let P : ℝ := (∑ n : Fin d, ((n.val+1 : ℕ) : ℝ))*harmonicFrequencyMass d
  have hP : 0 ≤ P := by dsimp [P, harmonicFrequencyMass]; positivity
  have ha : |2*actualShift T c| ≤ 1 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [actualShift_bounds T c]
  have hprod := finiteExponentialProduct_le_endpoint (centeredFrequency d)
    (2*actualShift T c) ha
  change finiteExponentialSum
      (fun n => integerLogFrequency d n-Real.log (d : ℝ)/2) (2*actualShift T c)*
      finiteExponentialSum (fun n => integerLogFrequency d n-Real.log (d : ℝ)/2)
        (-(2*actualShift T c)) ≤ _ at hprod
  rw [show finiteExponentialSum (centeredFrequency d) 1*
      finiteExponentialSum (centeredFrequency d) (-1) =
      finiteExponentialSum (integerLogFrequency d) 1*
        finiteExponentialSum (integerLogFrequency d) (-1) from
      finiteExponentialProduct_translate (integerLogFrequency d) (Real.log (d : ℝ)/2) 1,
    integerLogFrequency_endpoint_product] at hprod
  have hnorm :
      (‖actualExponentialVector T d c 1‖*
        ‖actualExponentialVector T d c (-1)‖)^2 ≤
          ((Ncount 0 T : ℝ)⁻¹)^2*P := by
    rw [mul_pow, actualExponentialVector_norm_sq, actualExponentialVector_norm_sq]
    rw [show (2 : ℝ)*1*actualShift T c = 2*actualShift T c by ring,
      show (2 : ℝ)*(-1)*actualShift T c = -(2*actualShift T c) by ring]
    calc
      _ = ((Ncount 0 T : ℝ)⁻¹)^2*
          (finiteExponentialSum (centeredFrequency d) (2*actualShift T c)*
            finiteExponentialSum (centeredFrequency d) (-(2*actualShift T c))) := by
        ring
      _ ≤ _ := by
        dsimp [P]
        exact mul_le_mul_of_nonneg_left hprod
          (sq_nonneg ((Ncount 0 T : ℝ)⁻¹))
  have hupper : ‖actualExponentialVector T d c 1‖*
      ‖actualExponentialVector T d c (-1)‖ ≤
        (Ncount 0 T : ℝ)⁻¹*Real.sqrt P := by
    have hs : ((Ncount 0 T : ℝ)⁻¹*Real.sqrt P)^2 =
        ((Ncount 0 T : ℝ)⁻¹)^2*P := by rw [mul_pow, Real.sq_sqrt hP]
    have h0 : 0 ≤ (Ncount 0 T : ℝ)⁻¹*Real.sqrt P := by positivity
    nlinarith [norm_nonneg (actualExponentialVector T d c 1),
      norm_nonneg (actualExponentialVector T d c (-1))]
  unfold actualHyperbolicCopyCap harmonicHyperbolicCap
  rw [actualExponentialVector_cross_re]
  dsimp [P] at hupper
  nlinarith

theorem badRealWeight_copy_sum (T δ : ℝ) :
    (∑ c : Copies T, badRealWeight δ c.1.1) = strictTail T δ := by
  rw [strictTail_eq_realSum, realSum_eq_copies]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases h : |c.1.1.re-1/2| ≤ δ
  · simp only [badRealWeight, if_pos h, if_neg (not_lt.mpr h)]
  · simp only [badRealWeight, if_neg h, if_pos (lt_of_not_ge h)]

theorem actualSignedTailBudget_le_harmonic (T : ℝ) (d : ℕ) (δ : ℝ) :
    actualSignedTailBudget T d δ ≤
      (strictTail T δ/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d := by
  unfold actualSignedTailBudget
  calc
    _ ≤ ∑ c : Copies T, badRealWeight δ c.1.1*
        ((Ncount 0 T : ℝ)⁻¹*harmonicHyperbolicCap d) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (actualHyperbolicCopyCap_le_harmonic T d c)
        (badRealWeight_nonneg δ c.1.1)
    _ = _ := by
      rw [← Finset.sum_mul, badRealWeight_copy_sum]
      simp only [div_eq_mul_inv]
      ring

theorem signedBadHyperbolic_upper_harmonic (T : ℝ) (d : ℕ) (δ : ℝ) :
    SignedBadHyperbolicUpper T d δ
      ((strictTail T δ/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d) := by
  intro f
  exact (signedBadHyperbolic_upper_budget T d δ f).trans
    (mul_le_mul_of_nonneg_right (actualSignedTailBudget_le_harmonic T d δ)
      (sq_nonneg ‖f‖))

theorem actualSignedTailBudget_le_log (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) :
    actualSignedTailBudget T d δ ≤
      (strictTail T δ/(Ncount 0 T : ℝ))*
        ((d : ℝ)/2*(1+Real.sqrt (1+Real.log (d : ℝ)))) :=
  (actualSignedTailBudget_le_harmonic T d δ).trans
    (mul_le_mul_of_nonneg_left (harmonicHyperbolicCap_le_log d hd)
      (div_nonneg (strictTail_nonneg T δ) (Nat.cast_nonneg _)))

open Filter in
theorem eventually_actualSignedTailBudget_le_third (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, ∀ δ : ℝ, 0 ≤ δ →
      actualSignedTailBudget T d δ ≤ (1/3+ε)*harmonicHyperbolicCap d := by
  filter_upwards [eventually_normalized_strictTail_le_third ε hε] with T hT
  intro d δ hδ
  exact (actualSignedTailBudget_le_harmonic T d δ).trans
    (mul_le_mul_of_nonneg_right (hT δ hδ) (harmonicHyperbolicCap_nonneg d))

open Filter in
theorem eventually_signedBadHyperbolic_upper_third (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, ∀ δ : ℝ, 0 ≤ δ →
      SignedBadHyperbolicUpper T d δ ((1/3+ε)*harmonicHyperbolicCap d) := by
  filter_upwards [eventually_actualSignedTailBudget_le_third ε hε] with T hT
  intro d δ hδ f
  exact (signedBadHyperbolic_upper_budget T d δ f).trans
    (mul_le_mul_of_nonneg_right (hT d δ hδ) (sq_nonneg ‖f‖))

theorem actualHyperbolicRow_form_neg_upper (T : ℝ) (d : ℕ)
    (c : Copies T) (f : Space d) :
    -(‖∑ n, f n*cosineRow (actualShift T) (centeredFrequency d)
          (actualPhaseRow T d) c n‖^2-
       ‖∑ n, f n*sineRow (actualShift T) (centeredFrequency d)
          (actualPhaseRow T d) c n‖^2) ≤
      actualHyperbolicCopyCap T d c*‖f‖^2 := by
  rw [actualHyperbolicRow_form_eq_cross]
  have h := rankTwoCross_form_neg_upper (actualExponentialVector T d c 1)
    (actualExponentialVector T d c (-1)) f
  have hcross : 0 ≤ (inner ℂ (actualExponentialVector T d c 1)
      (actualExponentialVector T d c (-1))).re := by
    rw [actualExponentialVector_cross_re]
    positivity
  have hcap :
      (‖actualExponentialVector T d c 1‖*
        ‖actualExponentialVector T d c (-1)‖-
        (inner ℂ (actualExponentialVector T d c 1)
          (actualExponentialVector T d c (-1))).re)/2 ≤
      actualHyperbolicCopyCap T d c := by
    unfold actualHyperbolicCopyCap
    linarith
  exact h.trans (mul_le_mul_of_nonneg_right hcap (sq_nonneg ‖f‖))

theorem actualSignedTailBudget_nonneg (T : ℝ) (d : ℕ) (δ : ℝ) :
    0 ≤ actualSignedTailBudget T d δ := by
  unfold actualSignedTailBudget
  apply Finset.sum_nonneg
  intro c hc
  apply mul_nonneg (badRealWeight_nonneg δ c.1.1)
  unfold actualHyperbolicCopyCap
  rw [actualExponentialVector_cross_re]
  positivity

theorem signedBadHyperbolic_form_neg_upper_budget (T : ℝ) (d : ℕ) (δ : ℝ)
    (f : Space d) :
    -(inner ℂ f (signedBadHyperbolic T d δ f)).re ≤
      actualSignedTailBudget T d δ*‖f‖^2 := by
  rw [signedBadHyperbolic_form_exact]
  unfold actualSignedTailBudget
  rw [Finset.sum_mul]
  calc
    _ = ∑ c : Copies T, badRealWeight δ c.1.1*
        -(‖∑ n, f n*cosineRow (actualShift T) (centeredFrequency d)
              (actualPhaseRow T d) c n‖^2-
           ‖∑ n, f n*sineRow (actualShift T) (centeredFrequency d)
              (actualPhaseRow T d) c n‖^2) := by
      simp only [mul_neg, Finset.sum_neg_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c hc
      have h := mul_le_mul_of_nonneg_left (actualHyperbolicRow_form_neg_upper T d c f)
        (badRealWeight_nonneg δ c.1.1)
      simpa only [mul_assoc] using h

theorem signedBadHyperbolic_form_abs_le_budget (T : ℝ) (d : ℕ) (δ : ℝ)
    (f : Space d) :
    |(inner ℂ f (signedBadHyperbolic T d δ f)).re| ≤
      actualSignedTailBudget T d δ*‖f‖^2 := by
  rw [abs_le]
  constructor
  · have h := signedBadHyperbolic_form_neg_upper_budget T d δ f
    linarith
  · exact signedBadHyperbolic_upper_budget T d δ f

theorem signedBadHyperbolic_isSelfAdjoint (T : ℝ) (d : ℕ) (δ : ℝ) :
    IsSelfAdjoint (signedBadHyperbolic T d δ) := by
  let M : Matrix (Fin d) (Fin d) ℂ :=
    fun n m => euclideanEntry (signedBadHyperbolic T d δ) n m
  have hentry (n m : Fin d) :
      star (euclideanEntry (signedBadHyperbolic T d δ) m n) =
        euclideanEntry (signedBadHyperbolic T d δ) n m := by
    rw [← signedBad_hyperbolic_entry, ← signedBad_hyperbolic_entry]
    exact hyperbolicKernel_star Finset.univ
      (fun c : Copies T => badRealWeight δ c.1.1)
      (actualShift T) (centeredFrequency d) (actualPhaseRow T d) n m
  have hM : star M = M := by
    ext n m
    exact hentry n m
  have hrep : signedBadHyperbolic T d δ =
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M := by
    apply euclideanEntry_ext
    intro n m
    exact (euclideanEntry_toEuclideanCLM M n m).symm
  rw [hrep]
  change star (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M) =
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M
  rw [← map_star, hM]

set_option maxHeartbeats 800000 in
theorem signedBadHyperbolic_norm_le_budget (T : ℝ) (d : ℕ) (δ : ℝ) :
    ‖signedBadHyperbolic T d δ‖ ≤ actualSignedTailBudget T d δ := by
  apply norm_le_of_abs_re_inner_le _ _ (actualSignedTailBudget_nonneg T d δ)
    (signedBadHyperbolic_isSelfAdjoint T d δ).isSymmetric
  exact signedBadHyperbolic_form_abs_le_budget T d δ

theorem signedBadHyperbolic_norm_le_harmonic (T : ℝ) (d : ℕ) (δ : ℝ) :
    ‖signedBadHyperbolic T d δ‖ ≤
      (strictTail T δ/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d :=
  (signedBadHyperbolic_norm_le_budget T d δ).trans
    (actualSignedTailBudget_le_harmonic T d δ)

theorem goodHyperbolic_norm_le_harmonic (T : ℝ) (d : ℕ) (δ : ℝ) :
    ‖goodHyperbolic T d δ‖ ≤ ‖landauGram T d‖+
      (strictTail T δ/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d := by
  exact (norm_sub_le (landauGram T d) (signedBadHyperbolic T d δ)).trans
    (add_le_add (le_refl _) (signedBadHyperbolic_norm_le_harmonic T d δ))

open Filter in
theorem eventually_signedBadHyperbolic_norm_le_third (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, ∀ δ : ℝ, 0 ≤ δ →
      ‖signedBadHyperbolic T d δ‖ ≤ (1/3+ε)*harmonicHyperbolicCap d := by
  filter_upwards [eventually_actualSignedTailBudget_le_third ε hε] with T hT
  intro d δ hδ
  exact (signedBadHyperbolic_norm_le_budget T d δ).trans (hT d δ hδ)

/-- The complementary rank-two coefficient is the positive cap minus the
actual cross mass d/N. No absolute-value loss is introduced. -/
theorem actualHyperbolicRow_form_neg_upper_correctedCap (T : ℝ) (d : ℕ)
    (c : Copies T) (f : Space d) :
    -(‖∑ n, f n*cosineRow (actualShift T) (centeredFrequency d)
          (actualPhaseRow T d) c n‖^2-
       ‖∑ n, f n*sineRow (actualShift T) (centeredFrequency d)
          (actualPhaseRow T d) c n‖^2) ≤
      (actualHyperbolicCopyCap T d c-(Ncount 0 T : ℝ)⁻¹*(d : ℝ))*‖f‖^2 := by
  rw [actualHyperbolicRow_form_eq_cross]
  have h := rankTwoCross_form_neg_upper (actualExponentialVector T d c 1)
    (actualExponentialVector T d c (-1)) f
  rw [actualExponentialVector_cross_re] at h
  have he :
      (‖actualExponentialVector T d c 1‖*
        ‖actualExponentialVector T d c (-1)‖-
        (Ncount 0 T : ℝ)⁻¹*(d : ℝ))/2 =
      actualHyperbolicCopyCap T d c-(Ncount 0 T : ℝ)⁻¹*(d : ℝ) := by
    unfold actualHyperbolicCopyCap
    rw [actualExponentialVector_cross_re]
    ring
  rw [he] at h
  exact h

/-- Exact sum of the complementary copy coefficients, preserving the strict
bad mask and all original multiplicities. -/
theorem actualCorrectedTailBudget_eq (T : ℝ) (d : ℕ) (δ : ℝ) :
    (∑ c : Copies T, badRealWeight δ c.1.1*
      (actualHyperbolicCopyCap T d c-(Ncount 0 T : ℝ)⁻¹*(d : ℝ))) =
      actualSignedTailBudget T d δ-
        (strictTail T δ/(Ncount 0 T : ℝ))*(d : ℝ) := by
  calc
    _ = (∑ c : Copies T, badRealWeight δ c.1.1*actualHyperbolicCopyCap T d c)-
        ∑ c : Copies T, badRealWeight δ c.1.1*((Ncount 0 T : ℝ)⁻¹*(d : ℝ)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = actualSignedTailBudget T d δ-
        strictTail T δ*((Ncount 0 T : ℝ)⁻¹*(d : ℝ)) := by
      rw [← Finset.sum_mul, badRealWeight_copy_sum]
      rfl
    _ = _ := by
      simp only [div_eq_mul_inv]
      ring

theorem signedBadHyperbolic_form_neg_upper_correctedBudget
    (T : ℝ) (d : ℕ) (δ : ℝ) (f : Space d) :
    -(inner ℂ f (signedBadHyperbolic T d δ f)).re ≤
      (actualSignedTailBudget T d δ-
        (strictTail T δ/(Ncount 0 T : ℝ))*(d : ℝ))*‖f‖^2 := by
  rw [signedBadHyperbolic_form_exact]
  calc
    _ = ∑ c : Copies T, badRealWeight δ c.1.1*
        -(‖∑ n, f n*cosineRow (actualShift T) (centeredFrequency d)
              (actualPhaseRow T d) c n‖^2-
           ‖∑ n, f n*sineRow (actualShift T) (centeredFrequency d)
              (actualPhaseRow T d) c n‖^2) := by
      simp only [mul_neg, Finset.sum_neg_distrib]
    _ ≤ (∑ c : Copies T, badRealWeight δ c.1.1*
        (actualHyperbolicCopyCap T d c-(Ncount 0 T : ℝ)⁻¹*(d : ℝ)))*‖f‖^2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro c hc
      have h := mul_le_mul_of_nonneg_left
        (actualHyperbolicRow_form_neg_upper_correctedCap T d c f)
        (badRealWeight_nonneg δ c.1.1)
      simpa only [mul_assoc] using h
    _ = _ := by rw [actualCorrectedTailBudget_eq]

/-- Sharp lower side paired with the already proved harmonic upper side. -/
theorem signedBadHyperbolic_form_neg_upper_harmonic
    (T : ℝ) (d : ℕ) (δ : ℝ) (f : Space d) :
    -(inner ℂ f (signedBadHyperbolic T d δ f)).re ≤
      ((strictTail T δ/(Ncount 0 T : ℝ))*
        (harmonicHyperbolicCap d-(d : ℝ)))*‖f‖^2 := by
  have hb := actualSignedTailBudget_le_harmonic T d δ
  have hcorrected : actualSignedTailBudget T d δ-
      (strictTail T δ/(Ncount 0 T : ℝ))*(d : ℝ) ≤
      (strictTail T δ/(Ncount 0 T : ℝ))*(harmonicHyperbolicCap d-(d : ℝ)) := by
    nlinarith
  exact (signedBadHyperbolic_form_neg_upper_correctedBudget T d δ f).trans
    (mul_le_mul_of_nonneg_right hcorrected (sq_nonneg ‖f‖))

set_option maxHeartbeats 800000 in
theorem signedBadHyperbolic_center_norm_le_harmonic (T : ℝ) (d : ℕ) (δ : ℝ) :
    ‖signedBadHyperbolic T d δ-
      (((strictTail T δ/(Ncount 0 T : ℝ))*(d : ℝ))/2) •
        (1 : Space d →L[ℂ] Space d)‖ ≤
      (strictTail T δ/(Ncount 0 T : ℝ))*(harmonicHyperbolicCap d-(d : ℝ)/2) := by
  let r : ℝ := strictTail T δ/(Ncount 0 T : ℝ)
  let lo : ℝ := -r*(harmonicHyperbolicCap d-(d : ℝ))
  let hi : ℝ := r*harmonicHyperbolicCap d
  have hr : 0 ≤ r := div_nonneg (strictTail_nonneg T δ) (Nat.cast_nonneg _)
  have hlohi : lo ≤ hi := by
    have hlo0 : lo ≤ 0 := by
      dsimp [lo]
      have h := mul_nonneg hr (harmonicHyperbolicCap_sub_card_nonneg d)
      nlinarith
    have hhi0 : 0 ≤ hi := mul_nonneg hr (harmonicHyperbolicCap_nonneg d)
    exact hlo0.trans hhi0
  have hlo : ∀ f : Space d, lo*‖f‖^2 ≤
      (inner ℂ f (signedBadHyperbolic T d δ f)).re := by
    intro f
    have h := signedBadHyperbolic_form_neg_upper_harmonic T d δ f
    dsimp [lo, r]
    nlinarith
  have hhi : ∀ f : Space d,
      (inner ℂ f (signedBadHyperbolic T d δ f)).re ≤ hi*‖f‖^2 := by
    exact signedBadHyperbolic_upper_harmonic T d δ
  have h := norm_sub_center_le_of_re_inner_interval (signedBadHyperbolic T d δ)
    lo hi hlohi (signedBadHyperbolic_isSelfAdjoint T d δ).isSymmetric hlo hhi
  have hc : (lo+hi)/2 = r*(d : ℝ)/2 := by dsimp [lo, hi]; ring
  have hR : (hi-lo)/2 = r*(harmonicHyperbolicCap d-(d : ℝ)/2) := by
    dsimp [lo, hi]
    ring
  rw [hc, hR] at h
  exact h

/-- Closed harmonic radius, with the shift explicitly r*d/2. -/
theorem signedBadHyperbolic_center_norm_le_closed_harmonic
    (T : ℝ) (d : ℕ) (δ : ℝ) :
    ‖signedBadHyperbolic T d δ-
      (((strictTail T δ/(Ncount 0 T : ℝ))*(d : ℝ))/2) •
        (1 : Space d →L[ℂ] Space d)‖ ≤
      (strictTail T δ/(Ncount 0 T : ℝ))/2*
        Real.sqrt ((d : ℝ)*((d : ℝ)+1)*(harmonic d : ℝ)/2) := by
  have h := signedBadHyperbolic_center_norm_le_harmonic T d δ
  have he :
      (strictTail T δ/(Ncount 0 T : ℝ))*(harmonicHyperbolicCap d-(d : ℝ)/2) =
      (strictTail T δ/(Ncount 0 T : ℝ))/2*
        Real.sqrt ((d : ℝ)*((d : ℝ)+1)*(harmonic d : ℝ)/2) := by
    rw [harmonicHyperbolicCap_eq]
    ring
  rw [he] at h
  exact h

end RiemannResearch.Analysis.ActualZeroPhaseMoments
