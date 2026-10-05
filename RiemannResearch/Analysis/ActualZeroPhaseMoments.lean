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
Identifying that operator series with the complete actual H-G correction,
including the complementary bad-zero part, remains a separate obligation.
-/

noncomputable section
open Complex Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate HorizontalEuclideanMoments HorizontalPhaseBootstrap

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
finite-copy provider. This theorem does not identify the series with the full
actual H-G correction; that exact operator identity remains a separate result. -/
theorem evenMomentCorrection_summable_and_norm_le
    (T : ℝ) (d : ℕ) (D : Space d →L[ℂ] Space d) (ell δ : ℝ)
    (hδ : 0 ≤ δ) (hD : 2 * ‖D‖ ≤ ell) :
    Summable (fun k => ‖evenTerm D (goodMoment T d δ) k‖) ∧
      Summable (evenTerm D (goodMoment T d δ)) ∧
      ‖∑' k, evenTerm D (goodMoment T d δ) k‖ ≤
        (‖phaseGram T d‖ / 2) * (Real.cosh (δ * ell) - 1) := by
  exact evenCorrection_summable_and_norm_le D (goodMoment T d δ) ell δ
    ‖phaseGram T d‖ hD (fun k => goodMoment_center_norm_le T d δ hδ (k + 1))

end RiemannResearch.Analysis.ActualZeroPhaseMoments
