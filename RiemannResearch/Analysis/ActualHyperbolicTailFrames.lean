/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualHyperbolicGramLowerBounds
import RiemannResearch.Analysis.HyperbolicRowNumericalRange
import RiemannResearch.Analysis.ActualZeroBadPhaseTail

/-!
# Actual signed bad-row budgets and masked centered frames

The bad hyperbolic operator keeps both cosine and negative sine channels,
the original full zero-count normalization and every multiplicity. The good
rows have the exact full-minus-bad form. The strongest directional surplus
provider is an equivalence; a one-sided upper provider feeds the concrete
centered-frame theorem. The unconditional finite rank-two budget supplies
that provider, but its asymptotic smallness is a separate application input.

Source: the user-requested actual hyperbolic lower-bound analysis (2026-10-05)
and the finite balanced-row proof in HyperbolicRowNumericalRange. The closed
harmonic cap is proved in ActualHyperbolicHarmonicTail. The published-density
specialization remains an analytic formalization obligation; see
RH/LeanProviderGapContinuation20261005.md.
-/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate ContinuousLinearMap RiemannResearch.Fourier HorizontalEuclideanMoments
open CenteredHyperbolicFrames ZeroOrdinate
local instance (T : ℝ) : DecidableEq (Copies T) := Classical.decEq _

def signedBadHyperbolic (T : ℝ) (d : ℕ) (δ : ℝ) : Space d →L[ℂ] Space d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (fun n m =>
    (Zeta23.Ncount 0 T : ℂ)⁻¹ * ActualZeroOrdinate.sum T (fun ρ =>
      ActualZeroOrdinate.badWeight δ ρ * ZeroOrdinate.phase (frequencyGap n m) ρ.im *
        (Real.cosh ((ρ.re-1/2)*frequencyGap n m) : ℂ)))
def goodHyperbolic (T : ℝ) (d : ℕ) (δ : ℝ) :=
  landauGram T d - signedBadHyperbolic T d δ

/-- The one-sided signed-tail provider, retaining the negative sinh square.
It is weaker than an absolute operator bound or a prescribed zero-density law. -/
def SignedBadHyperbolicUpper (T : ℝ) (d : ℕ) (δ B : ℝ) : Prop :=
  ∀ f : Space d, (inner ℂ f (signedBadHyperbolic T d δ f)).re ≤ B*‖f‖^2

theorem goodHyperbolic_form_lower_of_signedBad (T : ℝ) (d : ℕ) (δ B : ℝ)
    (hT : 0 ≤ T) (hbad : SignedBadHyperbolicUpper T d δ B) (f : Space d) :
    (actualHyperbolicLower T d-B)*‖f‖^2 ≤
      (inner ℂ f (goodHyperbolic T d δ f)).re := by
  have hfull := landauGram_form_lower T d hT f
  have hb := hbad f
  change actualHyperbolicLower T d*‖f‖^2 ≤ _ at hfull
  simp only [goodHyperbolic, sub_apply, inner_sub_right, Complex.sub_re]
  nlinarith

/-- Exact necessary-and-sufficient provider: allows the full form's surplus
in each coefficient direction, rather than replacing it by a worst-case bound. -/
theorem goodHyperbolic_lower_iff_signed_surplus (T : ℝ) (d : ℕ) (δ h : ℝ) :
    (∀ f : Space d, h*‖f‖^2 ≤ (inner ℂ f (goodHyperbolic T d δ f)).re) ↔
    (∀ f : Space d, (inner ℂ f (signedBadHyperbolic T d δ f)).re ≤
      (inner ℂ f (landauGram T d f)).re-h*‖f‖^2) := by
  simp only [goodHyperbolic, sub_apply, inner_sub_right, Complex.sub_re]
  constructor <;> intro hh f <;> have hf := hh f <;> linarith

theorem signedBadHyperbolic_entry (T : ℝ) (d : ℕ) (δ : ℝ) (n m : Fin d) :
    euclideanEntry (signedBadHyperbolic T d δ) n m =
      (Zeta23.Ncount 0 T : ℂ)⁻¹ * ActualZeroOrdinate.sum T (fun ρ =>
        badWeight δ ρ*phase (frequencyGap n m) ρ.im*
          (Real.cosh ((ρ.re-1/2)*frequencyGap n m) : ℂ)) :=
  euclideanEntry_toEuclideanCLM _ _ _

theorem signedBad_hyperbolic_entry (T : ℝ) (d : ℕ) (δ : ℝ) (n m : Fin d) :
    hyperbolicKernel Finset.univ (fun c : Copies T => badRealWeight δ c.1.1)
      (actualShift T) (centeredFrequency d) (actualPhaseRow T d) n m =
      euclideanEntry (signedBadHyperbolic T d δ) m n := by
  rw [signedBadHyperbolic_entry, sum_eq_copies, Finset.mul_sum]
  unfold hyperbolicKernel
  apply Finset.sum_congr rfl
  intro c hc
  have hh : Real.cosh (actualShift T c*
      (centeredFrequency d n-centeredFrequency d m)) =
      Real.cosh ((c.1.1.re-1/2)*frequencyGap m n) := by
    rw [show actualShift T c*(centeredFrequency d n-centeredFrequency d m) =
      -((c.1.1.re-1/2)*frequencyGap m n) by
        unfold actualShift centeredFrequency frequencyGap logFrequency; ring,
      Real.cosh_neg]
  calc
    _ = (badRealWeight δ c.1.1 : ℂ) *
      (Real.cosh (actualShift T c*(centeredFrequency d n-centeredFrequency d m)) : ℂ) *
      (actualPhaseRow T d c n*star (actualPhaseRow T d c m)) := by ring
    _ = _ := by rw [actualPhaseRow_product, hh, badRealWeight_coe]; ring

theorem signedBadHyperbolic_form_exact (T : ℝ) (d : ℕ) (δ : ℝ) (f : Space d) :
    (inner ℂ f (signedBadHyperbolic T d δ f)).re =
      ∑ c : Copies T, badRealWeight δ c.1.1 *
        (‖∑ n, f n*cosineRow (actualShift T) (centeredFrequency d)
            (actualPhaseRow T d) c n‖^2-
         ‖∑ n, f n*sineRow (actualShift T) (centeredFrequency d)
            (actualPhaseRow T d) c n‖^2) := by
  rw [← operator_inner_eq_transpose_form]
  simp_rw [← signedBad_hyperbolic_entry]
  rw [hyperbolic_form_factorization]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, zero_mul, mul_zero, sub_zero]

def actualGoodPhaseRow (T : ℝ) (d : ℕ) (δ : ℝ)
    (c : Copies T) (n : Fin d) : ℂ :=
  if |actualShift T c| ≤ δ then actualPhaseRow T d c n else 0
def actualGoodShift (T δ : ℝ) (c : Copies T) : ℝ :=
  if |actualShift T c| ≤ δ then actualShift T c else 0

theorem actualGoodShift_bounds (T δ : ℝ) (hδ : 0 ≤ δ) (c : Copies T) :
    |actualGoodShift T δ c| ≤ δ := by
  unfold actualGoodShift
  split_ifs with hc
  · exact hc
  · simpa using hδ

theorem actualGoodPhaseRow_hyperbolic_entry (T : ℝ) (d : ℕ) (δ : ℝ)
    (n m : Fin d) :
    hyperbolicKernel Finset.univ (fun _ : Copies T => (1 : ℝ))
      (actualGoodShift T δ) (centeredFrequency d) (actualGoodPhaseRow T d δ) n m =
      euclideanEntry (goodHyperbolic T d δ) m n := by
  rw [goodHyperbolic, euclideanEntry_sub,
    ← actualPhaseRow_hyperbolic_entry, ← signedBad_hyperbolic_entry]
  unfold hyperbolicKernel
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases ha : |actualShift T c| ≤ δ
  · have hw : badRealWeight δ c.1.1 = 0 := by
      simp only [badRealWeight, if_pos (show |c.1.1.re-1/2| ≤ δ from ha)]
    simp only [actualGoodShift, actualGoodPhaseRow, if_pos ha, hw,
      Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, sub_zero]
  · have hw : badRealWeight δ c.1.1 = 1 := by
      simp only [badRealWeight, if_neg (show ¬ |c.1.1.re-1/2| ≤ δ from ha)]
    simp only [actualGoodShift, actualGoodPhaseRow, if_neg ha, hw,
      Complex.ofReal_one, one_mul, star_zero, mul_zero, sub_self]

theorem actualGoodHyperbolic_rows_eq (T : ℝ) (d : ℕ) (δ : ℝ) (f : Space d) :
    ‖cosineAnalysis (actualGoodPhaseRow T d δ) (actualGoodShift T δ)
        (centeredFrequency d) f‖^2-
      ‖sineAnalysis (actualGoodPhaseRow T d δ) (actualGoodShift T δ)
        (centeredFrequency d) f‖^2 =
      (inner ℂ f (goodHyperbolic T d δ f)).re := by
  rw [← finite_hyperbolic_form_eq]
  have hkernel : hyperbolicKernel Finset.univ (fun _ : Copies T => (1 : ℝ))
      (actualGoodShift T δ) (centeredFrequency d) (actualGoodPhaseRow T d δ) =
      (fun n m => euclideanEntry (goodHyperbolic T d δ) m n) := by
    funext n m
    exact actualGoodPhaseRow_hyperbolic_entry T d δ n m
  rw [hkernel, operator_inner_eq_transpose_form]

/-- A concrete masked centered frame with only the explicit one-sided signed
bad-row provider left. Bad rows are zeroed, including their displacement. -/
theorem actual_good_centered_frame_lower_of_signedBad (T : ℝ) (d : ℕ) (δ B : ℝ)
    (hT : 0 ≤ T) (hd : 1 ≤ d) (hδ : 0 ≤ δ)
    (hbad : SignedBadHyperbolicUpper T d δ B)
    (hh : 0 ≤ actualHyperbolicLower T d-B) :
    ∀ f : Space d,
      ((Real.sqrt (actualHyperbolicLower T d-B)-
          ((Real.cosh (δ*(Real.log (d : ℝ)/2))-1)/2)*
            ‖rowAnalysis (actualGoodPhaseRow T d δ)‖) /
        ((1+Real.cosh (δ*(Real.log (d : ℝ)/2)))/2))*‖f‖ ≤
        ‖rowAnalysis (actualGoodPhaseRow T d δ) f‖ := by
  have hlog : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  apply finite_centered_frame_lower (actualGoodPhaseRow T d δ) (actualGoodShift T δ)
    (centeredFrequency d) (Real.log (d : ℝ)/2) δ (actualHyperbolicLower T d-B)
    (by positivity) hδ (actualGoodShift_bounds T δ hδ) (centeredFrequency_bounds d) hh
  intro f
  rw [actualGoodHyperbolic_rows_eq]
  exact goodHyperbolic_form_lower_of_signedBad T d δ B hT hbad f

/-- Exponential vectors whose inner products are the two actual signed row
channels. They use the original full zero-count normalization. -/
def actualExponentialVector (T : ℝ) (d : ℕ) (c : Copies T) (r : ℝ) : Space d :=
  WithLp.toLp 2 (fun n =>
    (Real.exp (r*actualShift T c*centeredFrequency d n) : ℂ) *
      star (actualPhaseRow T d c n))

theorem actualExponentialVector_inner (T : ℝ) (d : ℕ)
    (c : Copies T) (r : ℝ) (f : Space d) :
    inner ℂ (actualExponentialVector T d c r) f =
      ∑ n, f n*(Real.exp (r*actualShift T c*centeredFrequency d n) : ℂ)*
        actualPhaseRow T d c n := by
  rw [PiLp.inner_apply]
  change (∑ n, f n*star
    ((Real.exp (r*actualShift T c*centeredFrequency d n) : ℂ)*
      star (actualPhaseRow T d c n))) = _
  apply Finset.sum_congr rfl
  intro n hn
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  simp only [← Complex.star_def, star_star]
  ring

theorem actualCosineRow_sum_eq (T : ℝ) (d : ℕ)
    (c : Copies T) (f : Space d) :
    (∑ n, f n*cosineRow (actualShift T) (centeredFrequency d)
      (actualPhaseRow T d) c n) =
    (inner ℂ (actualExponentialVector T d c 1) f+
      inner ℂ (actualExponentialVector T d c (-1)) f)/(2 : ℂ) := by
  rw [actualExponentialVector_inner, actualExponentialVector_inner]
  simp only [one_mul, neg_one_mul, neg_mul]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [cosineRow, Real.cosh_eq]
  push_cast
  ring

theorem actualSineRow_sum_eq (T : ℝ) (d : ℕ)
    (c : Copies T) (f : Space d) :
    (∑ n, f n*sineRow (actualShift T) (centeredFrequency d)
      (actualPhaseRow T d) c n) =
    (inner ℂ (actualExponentialVector T d c 1) f-
      inner ℂ (actualExponentialVector T d c (-1)) f)/(2 : ℂ) := by
  rw [actualExponentialVector_inner, actualExponentialVector_inner]
  simp only [one_mul, neg_one_mul, neg_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [sineRow, Real.sinh_eq]
  push_cast
  ring

theorem actualHyperbolicRow_form_eq_cross (T : ℝ) (d : ℕ)
    (c : Copies T) (f : Space d) :
    ‖∑ n, f n*cosineRow (actualShift T) (centeredFrequency d)
      (actualPhaseRow T d) c n‖^2-
    ‖∑ n, f n*sineRow (actualShift T) (centeredFrequency d)
      (actualPhaseRow T d) c n‖^2 =
    (inner ℂ (actualExponentialVector T d c 1) f*
      star (inner ℂ (actualExponentialVector T d c (-1)) f)).re := by
  rw [actualCosineRow_sum_eq, actualSineRow_sum_eq, balancedRow_form_eq]

def actualHyperbolicCopyCap (T : ℝ) (d : ℕ) (c : Copies T) : ℝ :=
  (‖actualExponentialVector T d c 1‖*‖actualExponentialVector T d c (-1)‖+
    (inner ℂ (actualExponentialVector T d c 1)
      (actualExponentialVector T d c (-1))).re)/2

theorem actualHyperbolicRow_form_upper (T : ℝ) (d : ℕ)
    (c : Copies T) (f : Space d) :
    ‖∑ n, f n*cosineRow (actualShift T) (centeredFrequency d)
      (actualPhaseRow T d) c n‖^2-
    ‖∑ n, f n*sineRow (actualShift T) (centeredFrequency d)
      (actualPhaseRow T d) c n‖^2 ≤ actualHyperbolicCopyCap T d c*‖f‖^2 := by
  rw [actualHyperbolicRow_form_eq_cross]
  exact rankTwoCross_form_upper (actualExponentialVector T d c 1)
    (actualExponentialVector T d c (-1)) f

/-- A fully finite sufficient signed-tail budget, before prescribing any
zero-density estimate. Every copy and both row channels are retained. -/
def actualSignedTailBudget (T : ℝ) (d : ℕ) (δ : ℝ) : ℝ :=
  ∑ c : Copies T, badRealWeight δ c.1.1*actualHyperbolicCopyCap T d c

theorem signedBadHyperbolic_upper_budget (T : ℝ) (d : ℕ) (δ : ℝ) :
    SignedBadHyperbolicUpper T d δ (actualSignedTailBudget T d δ) := by
  intro f
  rw [signedBadHyperbolic_form_exact]
  unfold actualSignedTailBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c hc
  have h := mul_le_mul_of_nonneg_left (actualHyperbolicRow_form_upper T d c f)
    (badRealWeight_nonneg δ c.1.1)
  simpa only [mul_assoc] using h

end RiemannResearch.Analysis.ActualZeroPhaseMoments
