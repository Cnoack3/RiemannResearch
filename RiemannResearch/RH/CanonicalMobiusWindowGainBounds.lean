/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.CanonicalMobiusWindowDuality
import RiemannResearch.RH.AdjacentResidueHarmonic
import RiemannResearch.Analysis.FiniteGramScreeningCalculus

/-!
# Arithmetic window gains after exact Mobius-factor cancellation

Source: the user's request to resolve the PNT/dichotomy gap, 24 September
2026. The proof combines the repository's exact canonical Mobius step,
finite reciprocal-sum nonvanishing, actual Gram screening, and the complete
adjacent-residue harmonic identity. No novelty claim is made.

The same reciprocal Mobius factor occurs in the source and the screened
direction, and cancels from the gain. The remaining screened energy is
positive and at most H_(M+1). This gives a concrete lower bound for the
actual capacity by a sum of squared signed source pairings divided by
harmonic numbers. No divergence or RH hypothesis is assumed; divergence
of that source sum has not been proved.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto

open ArithmeticCumulative

theorem consecutiveResidueHilbert_sequence_eq_neg_adjacent (M j : ℕ) :
    hilbertSequence (consecutiveResidueHilbert M) j =
      -adjacentResidueDifference (M + 1) j := by
  rw [consecutiveResidueHilbert_sequence]
  unfold adjacentResidueDifference residueFraction residue
  have h1 : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((M + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : M + 1 + 1 = M + 2 := by omega
  rw [he]
  field_simp
  ring

theorem consecutiveResidueHilbert_energy_exact (M : ℕ) :
    ‖consecutiveResidueHilbert M‖ ^ 2 =
      (harmonic (M + 1) : ℝ) - ((M + 1 : ℕ) : ℝ) / (((M + 1 : ℕ) : ℝ) + 1) +
        adjacentResidueRemainder (M + 1) := by
  rw [hilbert_norm_weighted_sq]
  simp_rw [consecutiveResidueHilbert_sequence_eq_neg_adjacent, neg_sq]
  exact adjacentResidueDifference_energy_exact (M + 1) (by omega)

theorem consecutiveResidueHilbert_energy_le_harmonic (M : ℕ) :
    ‖consecutiveResidueHilbert M‖ ^ 2 ≤ (harmonic (M + 1) : ℝ) := by
  rw [hilbert_norm_weighted_sq]
  simp_rw [consecutiveResidueHilbert_sequence_eq_neg_adjacent, neg_sq]
  exact adjacentResidueDifference_energy_upper (M + 1) (by omega)

theorem consecutiveResidueHilbert_tail_energy_le_harmonic (N M : ℕ) :
    ‖hilbertTailShift (consecutiveResidueHilbert M) N‖ ^ 2 ≤
      (harmonic (M + 1) : ℝ) := by
  rw [hilbertTailShift_norm_sq]
  exact (sub_le_self _ (Finset.sum_nonneg (fun i hi => sq_nonneg _))).trans
    (consecutiveResidueHilbert_energy_le_harmonic M)

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance

open RiemannResearch.Analysis.FiniteHilbertGram

def windowStepTail (N M : ℕ) : ThresholdHilbert :=
  hilbertTailShift (consecutiveResidueHilbert M) N

theorem canonicalMobiusTail_succ (N M : ℕ) :
    hilbertTailShift (canonicalMobiusHilbert (M + 1)) N =
      hilbertTailShift (canonicalMobiusHilbert M) N +
        mobiusReciprocalSum (M + 1) • windowStepTail N M := by
  have hs := congrArg (hilbertTailShiftLinear N) (canonicalMobiusHilbert_succ_sub M)
  simp only [map_sub, map_smul] at hs
  exact sub_eq_iff_eq_add'.mp hs

theorem windowDefect_eq_mobius_step_pairing (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    oneStepDefect N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN) (M + 1) =
      -mobiusReciprocalSum (M + 1) * inner ℝ (windowStepTail N M) (windowNormal N M hN) := by
  unfold oneStepDefect
  rw [canonicalMobiusTail_succ, inner_add_left, real_inner_smul_left]
  change 1 - (inner ℝ (hilbertTailShift (canonicalMobiusHilbert M) N)
    (windowNormal N M hN) + _) = _
  rw [windowNormal_equation N M M hN hNM le_rfl]
  dsimp [windowNormal]
  ring

theorem windowSchur_eq_mobius_sq_step_energy (N M : ℕ) (hNM : N ≤ M) :
    oneStepSchur N (canonicalWindowIndex N M) (M + 1) =
      mobiusReciprocalSum (M + 1) ^ 2 *
        ‖screenedVector (tailFamily N (canonicalWindowIndex N M)) (windowStepTail N M)‖ ^ 2 := by
  let i : Fin (M - N + 1) := ⟨M - N, by omega⟩
  have hi : canonicalWindowIndex N M i = M := by
    dsimp [canonicalWindowIndex, i]
    omega
  have he : hilbertTailShift (canonicalMobiusHilbert M) N =
      tailFamily N (canonicalWindowIndex N M) i := by simp only [tailFamily, hi]
  rw [oneStepSchur, canonicalMobiusTail_succ, he, screenedVector_add_family_smul,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem windowGain_eq_step_pairing_quotient (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    windowGain N M hN =
      (inner ℝ (windowStepTail N M) (windowNormal N M hN)) ^ 2 /
        ‖screenedVector (tailFamily N (canonicalWindowIndex N M)) (windowStepTail N M)‖ ^ 2 := by
  have hm : mobiusReciprocalSum (M + 1) ≠ 0 := mobiusReciprocalSum_ne_zero (by omega)
  rw [windowGain, windowDefect_eq_mobius_step_pairing N M hN hNM,
    windowSchur_eq_mobius_sq_step_energy N M hNM, mul_pow, neg_sq]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hm)

end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance

open RiemannResearch.Analysis.FiniteHilbertGram

theorem windowStepScreened_energy_pos (N M : ℕ) (hNM : N ≤ M) :
    0 < ‖screenedVector (tailFamily N (canonicalWindowIndex N M))
      (windowStepTail N M)‖ ^ 2 := by
  have hs := oneStepSchur_succ_pos N M (canonicalWindowIndex N M) (fun i => by
    simp only [canonicalWindowIndex]
    have hi := i.isLt
    omega)
  rw [windowSchur_eq_mobius_sq_step_energy N M hNM] at hs
  by_contra! hn
  have hm := sq_nonneg (mobiusReciprocalSum (M + 1))
  have hp := mul_nonpos_of_nonneg_of_nonpos hm hn
  linarith

theorem windowStepScreened_energy_le_harmonic (N M : ℕ) :
    ‖screenedVector (tailFamily N (canonicalWindowIndex N M))
      (windowStepTail N M)‖ ^ 2 ≤ (harmonic (M + 1) : ℝ) :=
  (screenedVector_norm_sq_le _ _).trans
    (consecutiveResidueHilbert_tail_energy_le_harmonic N M)

theorem windowGain_harmonic_source_lower (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    (inner ℝ (windowStepTail N M) (windowNormal N M hN)) ^ 2 /
      (harmonic (M + 1) : ℝ) ≤ windowGain N M hN := by
  rw [windowGain_eq_step_pairing_quotient N M hN hNM]
  exact div_le_div_of_nonneg_left (sq_nonneg _)
    (windowStepScreened_energy_pos N M hNM)
    (windowStepScreened_energy_le_harmonic N M)

theorem windowCapacity_harmonic_source_lower (N L : ℕ) (hN : 0 < N) :
    (‖hilbertTailShift (canonicalMobiusHilbert N) N‖ ^ 2)⁻¹ +
      (∑ j ∈ Finset.range L,
        (inner ℝ (windowStepTail N (N + j)) (windowNormal N (N + j) hN)) ^ 2 /
          (harmonic (N + j + 1) : ℝ)) ≤ windowCapacity N (N + L) hN := by
  rw [windowCapacity_eq_base_add_gains]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j hj
  exact windowGain_harmonic_source_lower N (N + j) hN (by omega)

end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
