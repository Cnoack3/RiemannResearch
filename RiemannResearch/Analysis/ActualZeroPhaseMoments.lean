/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.HorizontalEuclideanMoments
import RiemannResearch.Analysis.HorizontalPhaseBootstrap

/-!
# Complete actual-zero phase Gram and horizontal moments

Every copy of every actual nontrivial zeta zero in (0,T] remains in the
original finite index set. Both the full Gram and every masked moment use
the original actual `Ncount 0 T` normalizer. Every integer frequency 1,...,d
is present. Norms are Euclidean continuous-operator norms.

The actual finite-copy theorem discharges the centered-moment norm premise
of HorizontalPhaseBootstrap. Its commutator series is absolutely summable.
The zeroth masked Gram dominates every higher good moment and is itself
bounded in norm by the full phase Gram. The complete actual H-G identity,
including the signed complementary bad-zero part, is proved in
ActualZeroPhaseOperators.
-/

noncomputable section
open Complex Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate HorizontalEuclideanMoments HorizontalPhaseBootstrap
open ContinuousLinearMap

abbrev Space (d : ℕ) := EuclideanSpace ℂ (Fin d)

def phaseGram (T : ℝ) (d : ℕ) : Space d →L[ℂ] Space d :=
  copyGram (Finset.univ : Finset (Copies T)) (Ncount 0 T : ℝ)⁻¹
    (fun c => copyPhaseVector d c.1.1)

def goodMoment (T : ℝ) (d : ℕ) (δ : ℝ) (k : ℕ) : Space d →L[ℂ] Space d :=
  weightedCopyGram (Finset.univ : Finset (Copies T)) (Ncount 0 T : ℝ)⁻¹
    (fun c => goodEvenWeight δ k c.1.1) (fun c => copyPhaseVector d c.1.1)

theorem phaseGram_eq_finitePhaseGram (T : ℝ) (d : ℕ) :
    phaseGram T d = finitePhaseGram d (Finset.univ : Finset (Copies T))
      (fun c => c.1.1) := by
  simp only [phaseGram, finitePhaseGram, Finset.card_univ, card_copies]

theorem phaseGram_positive (T : ℝ) (d : ℕ) :
    (phaseGram T d).IsPositive := by
  have h := weightedCopyGram_positive (Finset.univ : Finset (Copies T))
    (Ncount 0 T : ℝ)⁻¹ (fun _ => (1 : ℝ))
    (fun c => copyPhaseVector d c.1.1) (by positivity) (fun _ _ => by norm_num)
  simpa only [weightedCopyGram, phaseGram, copyGram, one_smul] using h

theorem goodMoment_positive (T : ℝ) (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) :
    (goodMoment T d δ k).IsPositive := by
  apply weightedCopyGram_positive
  · positivity
  · intro c hc
    exact (goodEvenWeight_bounds δ hδ k c.1.1).1

theorem goodMoment_center_norm_le (T : ℝ) (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) :
    ‖goodMoment T d δ k -
      (δ ^ (2 * k) * ‖phaseGram T d‖ / 2) • (1 : Space d →L[ℂ] Space d)‖ ≤
      δ ^ (2 * k) * ‖phaseGram T d‖ / 2 := by
  unfold goodMoment phaseGram
  apply weightedCopyGram_center_norm_le
  · positivity
  · positivity
  · intro c hc
    exact goodEvenWeight_bounds δ hδ k c.1.1

/-- The old abstract centered-moment norm premise is discharged by the actual
finite-copy provider. The exact full actual H-G operator identity is proved
in ActualZeroPhaseOperators. -/
theorem evenMomentCorrection_summable_and_norm_le
    (T : ℝ) (d : ℕ) (D : Space d →L[ℂ] Space d) (ell δ : ℝ)
    (hδ : 0 ≤ δ) (hD : 2 * ‖D‖ ≤ ell) :
    Summable (fun k => ‖evenTerm D (goodMoment T d δ) k‖) ∧
      Summable (evenTerm D (goodMoment T d δ)) ∧
      ‖∑' k, evenTerm D (goodMoment T d δ) k‖ ≤
        (‖phaseGram T d‖ / 2) * (Real.cosh (δ * ell) - 1) := by
  exact evenCorrection_summable_and_norm_le D (goodMoment T d δ) ell δ
    ‖phaseGram T d‖ hD (fun k => goodMoment_center_norm_le T d δ hδ (k + 1))

/-- Exact signed difference before applying positivity or a norm estimate. -/
theorem goodMoment_domination_identity
    (T : ℝ) (d : ℕ) (δ : ℝ) (k : ℕ) :
    δ ^ (2 * k) • goodMoment T d δ 0 - goodMoment T d δ k =
      weightedCopyGram
        (Finset.univ : Finset (Copies T))
        (Ncount 0 T : ℝ)⁻¹
        (fun c =>
          δ ^ (2 * k) * goodEvenWeight δ 0 c.1.1 -
            goodEvenWeight δ k c.1.1)
        (fun c => copyPhaseVector d c.1.1) := by
  unfold goodMoment weightedCopyGram
  simp only [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hcoeff :
      (Ncount 0 T : ℝ)⁻¹ *
          (δ ^ (2 * k) * goodEvenWeight δ 0 c.1.1 -
            goodEvenWeight δ k c.1.1) =
        δ ^ (2 * k) *
            ((Ncount 0 T : ℝ)⁻¹ * goodEvenWeight δ 0 c.1.1) -
          (Ncount 0 T : ℝ)⁻¹ * goodEvenWeight δ k c.1.1 := by
    ring
  rw [hcoeff]
  exact (sub_smul
    (δ ^ (2 * k) *
      ((Ncount 0 T : ℝ)⁻¹ * goodEvenWeight δ 0 c.1.1))
    ((Ncount 0 T : ℝ)⁻¹ * goodEvenWeight δ k c.1.1)
    (InnerProductSpace.rankOne ℂ
      (copyPhaseVector d c.1.1) (copyPhaseVector d c.1.1))).symm

/-- The complete actual masked difference is positive. -/
theorem goodMoment_domination_positive
    (T : ℝ) (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) :
    (δ ^ (2 * k) • goodMoment T d δ 0 -
      goodMoment T d δ k).IsPositive := by
  rw [goodMoment_domination_identity]
  apply weightedCopyGram_positive
  · positivity
  · intro c hc
    exact sub_nonneg.mpr
      (goodEvenWeight_le_zeroth δ hδ k c.1.1)

/-- Refined centering uses the actual good-copy Gram, rather than the full
Gram. The original actual-zero normalizer is unchanged. -/
theorem goodMoment_center_norm_le_zeroth
    (T : ℝ) (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) :
    ‖goodMoment T d δ k -
      (δ ^ (2 * k) * ‖goodMoment T d δ 0‖ / 2) •
        (1 : Space d →L[ℂ] Space d)‖ ≤
      δ ^ (2 * k) * ‖goodMoment T d δ 0‖ / 2 := by
  have hp := goodMoment_positive T d δ hδ k
  have hd := goodMoment_domination_positive T d δ hδ k
  apply norm_center_le_of_qform_bounds _
    (δ ^ (2 * k) * ‖goodMoment T d δ 0‖)
    (mul_nonneg (by positivity) (norm_nonneg _))
    hp.isSymmetric hp.2
  intro x
  have hh := hd.2 x
  rw [qform_sub, qform_real_smul] at hh
  calc
    _ ≤ δ ^ (2 * k) *
        (goodMoment T d δ 0).reApplyInnerSelf x := by
      linarith
    _ ≤ δ ^ (2 * k) *
        (‖goodMoment T d δ 0‖ * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (qform_le_norm _ _) (by positivity)
    _ = _ := by ring

/-- Higher masked moments are dominated in norm by the zeroth actual masked
Gram, retaining every original copy and the original count normalizer. -/
theorem goodMoment_norm_le_zeroth
    (T : ℝ) (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) :
    ‖goodMoment T d δ k‖ ≤
      δ ^ (2 * k) * ‖goodMoment T d δ 0‖ := by
  apply norm_le_of_positive_qform_upper_bound _
    (δ ^ (2 * k) * ‖goodMoment T d δ 0‖)
    (mul_nonneg (by positivity) (norm_nonneg _))
    (goodMoment_positive T d δ hδ k)
  intro x
  have hh := (goodMoment_domination_positive T d δ hδ k).2 x
  rw [qform_sub, qform_real_smul] at hh
  calc
    _ ≤ δ ^ (2 * k) *
        (goodMoment T d δ 0).reApplyInnerSelf x := by linarith
    _ ≤ δ ^ (2 * k) *
        (‖goodMoment T d δ 0‖ * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (qform_le_norm _ _) (by positivity)
    _ = _ := by ring

/-- The smaller zeroth masked norm is bounded by the full actual Gram norm.
The proof uses the exact generic rank-one domination identity, so the
normalizer and every composite-frequency interaction remain unchanged. -/
theorem goodMoment_zeroth_norm_le_phaseGram
    (T : ℝ) (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖goodMoment T d δ 0‖ ≤ ‖phaseGram T d‖ := by
  apply norm_le_of_positive_domination _ _
    (goodMoment_positive T d δ hδ 0)
  have hdom : phaseGram T d - goodMoment T d δ 0 =
      weightedCopyGram
        (Finset.univ : Finset (Copies T))
        (Ncount 0 T : ℝ)⁻¹
        (fun c => 1 - goodEvenWeight δ 0 c.1.1)
        (fun c => copyPhaseVector d c.1.1) := by
    simpa only [phaseGram, goodMoment, one_smul] using
      weightedCopyGram_domination_identity
        (Finset.univ : Finset (Copies T))
        (Ncount 0 T : ℝ)⁻¹ 1
        (fun c => goodEvenWeight δ 0 c.1.1)
        (fun c => copyPhaseVector d c.1.1)
  rw [hdom]
  apply weightedCopyGram_positive
  · positivity
  · intro c hc
    simpa only [Nat.mul_zero, pow_zero] using
      sub_nonneg.mpr (goodEvenWeight_bounds δ hδ 0 c.1.1).2

/-- Absolute convergence and the sharp half-factor bound using the actual
good-copy Gram norm. No analytic distribution premise occurs. -/
theorem evenGoodCorrection_summable_and_norm_le_zeroth
    (T : ℝ) (d : ℕ)
    (D : Space d →L[ℂ] Space d) (ell δ : ℝ)
    (hδ : 0 ≤ δ) (hD : 2 * ‖D‖ ≤ ell) :
    Summable
        (fun k => ‖evenTerm D (goodMoment T d δ) k‖) ∧
      Summable (evenTerm D (goodMoment T d δ)) ∧
      ‖∑' k, evenTerm D (goodMoment T d δ) k‖ ≤
        (‖goodMoment T d δ 0‖ / 2) *
          (Real.cosh (δ * ell) - 1) := by
  exact evenCorrection_summable_and_norm_le
    D (goodMoment T d δ) ell δ
    ‖goodMoment T d δ 0‖ hD
    (fun k =>
      goodMoment_center_norm_le_zeroth
        T d δ hδ (k + 1))

end RiemannResearch.Analysis.ActualZeroPhaseMoments
