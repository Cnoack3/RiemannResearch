/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroLogDiagonal
import RiemannResearch.Analysis.ActualZeroHorizontalExpansion
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact horizontal correction of the actual phase-Gram operator

The full Landau operator minus the ordinate Gram operator is the complete even
commutator series plus the signed complementary bad-copy correction. Matrix
entries use frequencies 1,...,d and the original actual-zero copy normalizer;
all analytic multiplicities and both masks are retained before taking norms.

The centered log diagonal and the actual positive moments supply every finite
operator provider. The complete good correction has the factor one half from
positive-operator centering. These identities require no Landau, zero-density,
simplicity or RH estimate. Source: the user-provided phase-Gram argument and
RH/GrowingPhaseGramBootstrapAudit20261005.md.
-/

noncomputable section
open Complex Zeta23
open scoped BigOperators InnerProductSpace Matrix

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments

open ActualZeroOrdinate HorizontalEuclideanMoments HorizontalPhaseBootstrap
open ZeroOrdinate ContinuousLinearMap

def frequencyGap {d : ℕ} (n m : Fin d) : ℝ :=
  Real.log ((n.val + 1 : ℕ) : ℝ) - Real.log ((m.val + 1 : ℕ) : ℝ)

theorem copyPhaseVector_apply (d : ℕ) (ρ : ℂ) (n : Fin d) :
    copyPhaseVector d ρ n = phase (Real.log ((n.val + 1 : ℕ) : ℝ)) ρ.im := by
  change Complex.exp (((ρ.im * Real.log ((n.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) = _
  unfold phase
  congr 1
  push_cast
  ring

theorem copyPhaseVector_kernel (d : ℕ) (ρ : ℂ) (n m : Fin d) :
    copyPhaseVector d ρ n * star (copyPhaseVector d ρ m) =
      phase (frequencyGap n m) ρ.im := by
  rw [copyPhaseVector_apply, copyPhaseVector_apply, ← phase_neg]
  simpa only [frequencyGap, sub_eq_add_neg] using
    (phase_add (Real.log ((n.val + 1 : ℕ) : ℝ))
      (-Real.log ((m.val + 1 : ℕ) : ℝ)) ρ.im).symm

theorem goodEvenWeight_coe (δ : ℝ) (k : ℕ) (ρ : ℂ) :
    (goodEvenWeight δ k ρ : ℂ) =
      goodWeight δ ρ * ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ (2 * k) := by
  by_cases h : |ρ.re - 1 / 2| ≤ δ
  · simp only [goodEvenWeight, goodWeight, if_pos h, one_mul]
    push_cast
    rfl
  · simp only [goodEvenWeight, goodWeight, if_neg h, Complex.ofReal_zero, zero_mul]

/-- Exact VV* orientation: the (n,m) phase has frequency log(n+1)-log(m+1). -/
theorem phaseGram_entry (T : ℝ) (d : ℕ) (n m : Fin d) :
    euclideanEntry (phaseGram T d) n m =
      (Ncount 0 T : ℂ)⁻¹ * ordinateSum T (frequencyGap n m) := by
  have hs : euclideanEntry
      (∑ c : Copies T, InnerProductSpace.rankOne ℂ
        (copyPhaseVector d c.1.1) (copyPhaseVector d c.1.1)) n m =
      ordinateSum T (frequencyGap n m) := by
    rw [← euclideanEntryCLM_apply, map_sum]
    simp_rw [euclideanEntryCLM_apply, euclideanEntry_rankOne, copyPhaseVector_kernel]
    rw [ordinateSum, sum_eq_copies]
  unfold phaseGram copyGram
  rw [euclideanEntry_real_smul, hs]
  push_cast
  rfl

/-- Exact actual finite even horizontal moment entry, with all multiplicities
and the original full-copy normalizer. -/
theorem goodMoment_entry (T : ℝ) (d : ℕ) (δ : ℝ) (k : ℕ) (n m : Fin d) :
    euclideanEntry (goodMoment T d δ k) n m =
      (Ncount 0 T : ℂ)⁻¹ * sum T (fun ρ =>
        goodWeight δ ρ * phase (frequencyGap n m) ρ.im *
          ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ (2 * k)) := by
  have hs : euclideanEntry
      (∑ c : Copies T, goodEvenWeight δ k c.1.1 •
        InnerProductSpace.rankOne ℂ (copyPhaseVector d c.1.1) (copyPhaseVector d c.1.1))
        n m = sum T (fun ρ =>
        goodWeight δ ρ * phase (frequencyGap n m) ρ.im *
          ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ (2 * k)) := by
    rw [← euclideanEntryCLM_apply, map_sum]
    simp_rw [euclideanEntryCLM_apply, euclideanEntry_real_smul,
      euclideanEntry_rankOne, copyPhaseVector_kernel, goodEvenWeight_coe]
    rw [sum_eq_copies]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  unfold goodMoment weightedCopyGram
  rw [euclideanEntry_real_smul, hs]
  push_cast
  rfl

/-- Full actual centered Landau operator, retaining every integer frequency. -/
def landauGram (T : ℝ) (d : ℕ) : Space d →L[ℂ] Space d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (fun n m : Fin d =>
    (Ncount 0 T : ℂ)⁻¹ * landauSum T (frequencyGap n m))

/-- Signed complementary bad-copy correction. No absolute value or copy is lost. -/
def badCorrection (T : ℝ) (d : ℕ) (δ : ℝ) : Space d →L[ℂ] Space d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (fun n m : Fin d =>
    (Ncount 0 T : ℂ)⁻¹ *
      weightedCoshCorrection T (frequencyGap n m) (badWeight δ))

@[simp] theorem landauGram_entry (T : ℝ) (d : ℕ) (n m : Fin d) :
    euclideanEntry (landauGram T d) n m =
      (Ncount 0 T : ℂ)⁻¹ * landauSum T (frequencyGap n m) :=
  euclideanEntry_toEuclideanCLM _ _ _

@[simp] theorem badCorrection_entry (T : ℝ) (d : ℕ) (δ : ℝ) (n m : Fin d) :
    euclideanEntry (badCorrection T d δ) n m =
      (Ncount 0 T : ℂ)⁻¹ * weightedCoshCorrection T (frequencyGap n m) (badWeight δ) :=
  euclideanEntry_toEuclideanCLM _ _ _

/-- The complete original signed scalar correction splits into the exact good
and complementary bad corrections before applying any estimate. -/
theorem landau_minus_ordinate_split (T u δ : ℝ) :
    landauSum T u - ordinateSum T u =
      weightedCoshCorrection T u (goodWeight δ) +
      weightedCoshCorrection T u (badWeight δ) := by
  have h := exact_signed_correction T u
  have hs := weighted_sum_split T δ (fun ρ =>
    phase u ρ.im * ((Real.cosh (u * (ρ.re - 1 / 2)) : ℂ) - 1))
  have hs' : coshCorrection T u =
    weightedCoshCorrection T u (goodWeight δ) +
    weightedCoshCorrection T u (badWeight δ) := by
    simpa only [coshCorrection, weightedCoshCorrection, mul_assoc] using hs
  rw [hs'] at h
  linear_combination -h

theorem evenTerm_entry_of_diagonal
    (T : ℝ) (d : ℕ) (D : Space d →L[ℂ] Space d) (δ : ℝ)
    (hentry : ∀ j (A : Space d →L[ℂ] Space d) (n m : Fin d),
      euclideanEntry (iterComm D j A) n m =
        (frequencyGap n m : ℂ) ^ j * euclideanEntry A n m)
    (k : ℕ) (n m : Fin d) :
    euclideanEntry (evenTerm D (goodMoment T d δ) k) n m =
      (Ncount 0 T : ℂ)⁻¹ *
        ((Nat.factorial (2 * (k + 1)) : ℂ)⁻¹ *
          (frequencyGap n m : ℂ) ^ (2 * (k + 1)) *
            sum T (fun ρ => goodWeight δ ρ * phase (frequencyGap n m) ρ.im *
              ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ (2 * (k + 1)))) := by
  rw [evenTerm, euclideanEntry_real_smul, hentry, goodMoment_entry]
  push_cast
  ring

theorem evenCorrection_entry_of_diagonal
    (T : ℝ) (d : ℕ) (D : Space d →L[ℂ] Space d) (ell δ : ℝ)
    (hδ : 0 ≤ δ) (hD : 2 * ‖D‖ ≤ ell)
    (hentry : ∀ j (A : Space d →L[ℂ] Space d) (n m : Fin d),
      euclideanEntry (iterComm D j A) n m =
        (frequencyGap n m : ℂ) ^ j * euclideanEntry A n m)
    (n m : Fin d) :
    euclideanEntry (∑' k, evenTerm D (goodMoment T d δ) k) n m =
      (Ncount 0 T : ℂ)⁻¹ *
        weightedCoshCorrection T (frequencyGap n m) (goodWeight δ) := by
  have hs := (evenMomentCorrection_summable_and_norm_le T d D ell δ hδ hD).2.1
  rw [euclideanEntry_tsum _ hs]
  simp_rw [evenTerm_entry_of_diagonal T d D δ hentry]
  rw [tsum_mul_left, weightedCoshCorrection_eq_tsum_evenMoments]

/-- Complete actual normalized operator correction, retaining the signed bad
copy remainder. The actual diagonal entry provider discharges hentry. -/
theorem landauGram_sub_phaseGram_of_diagonal
    (T : ℝ) (d : ℕ) (D : Space d →L[ℂ] Space d) (ell δ : ℝ)
    (hδ : 0 ≤ δ) (hD : 2 * ‖D‖ ≤ ell)
    (hentry : ∀ j (A : Space d →L[ℂ] Space d) (n m : Fin d),
      euclideanEntry (iterComm D j A) n m =
        (frequencyGap n m : ℂ) ^ j * euclideanEntry A n m) :
    landauGram T d - phaseGram T d =
      (∑' k, evenTerm D (goodMoment T d δ) k) + badCorrection T d δ := by
  apply euclideanEntry_ext
  intro n m
  rw [euclideanEntry_sub, landauGram_entry, phaseGram_entry,
    euclideanEntry_add, evenCorrection_entry_of_diagonal T d D ell δ hδ hD hentry,
    badCorrection_entry]
  rw [← mul_sub, landau_minus_ordinate_split]
  ring

/-- Full actual centered-log operator identity with every algebraic provider
discharged. The finite support assumption d>=1 supplies the diagonal norm
bound; no analytic distribution premise occurs. -/
theorem landauGram_sub_phaseGram
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ) :
    landauGram T d - phaseGram T d =
      (∑' k, evenTerm (logDiagonal d) (goodMoment T d δ) k) +
        badCorrection T d δ := by
  apply landauGram_sub_phaseGram_of_diagonal T d (logDiagonal d) (Real.log (d : ℝ)) δ
    hδ (two_mul_logDiagonal_norm_le d hd)
  intro j A n m
  simpa only [euclideanEntry, frequencyGap, logFrequency] using
    iterComm_logDiagonal_apply_single d A j n m

set_option maxHeartbeats 800000 in
/-- Actual complete correction norm bound with the exact complementary bad
operator retained. Uniform arithmetic/zero-density estimates are not presumed. -/
theorem norm_landauGram_sub_phaseGram_le
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖landauGram T d - phaseGram T d‖ ≤
      (‖phaseGram T d‖ / 2) * (Real.cosh (δ * Real.log (d : ℝ)) - 1) +
        ‖badCorrection T d δ‖ := by
  have hb := (logEvenMomentCorrection_summable_and_norm_le T d hd δ hδ).2.2
  have ha := norm_add_le
    (∑' k, evenTerm (logDiagonal d) (goodMoment T d δ) k) (badCorrection T d δ)
  rw [landauGram_sub_phaseGram T d hd δ hδ]
  linarith only [ha, hb]

end RiemannResearch.Analysis.ActualZeroPhaseMoments
