/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTSquarefreeBoundedTail
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.LocalizedMellinObstruction
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# Explicit power obstruction for exact-head CRT tails

Source: user-provided exact-head CRT formulation, 13 October 2026.
An actual off-critical zeta zero forces a positive power of the head length.
This is an unconditional obstruction, not a construction of bounded tails.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer
open ParetoBeurlingMellinObstruction

/-- The complete Pareto error has the sharper factor zeta(2), not two. -/
theorem periodic_error_le_zetaTwo_mul_reciprocalEnergy
    (L : ℕ) (hL : 0 < L) (f : ThresholdHilbert)
    {C : ℝ} (hf : ∀ n, |hilbertSequence f n| ≤ C)
    (hp : ∀ n, hilbertSequence f (n + L) = hilbertSequence f n) :
    ‖hilbertOne - f‖ ^ 2 ≤ zetaTwo *
      crtReciprocalEnergy L (fun n => 1 - hilbertSequence f n) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf 0)
  let q := encodeQ (hilbertSequence f)
    (boundedQ_square_summable _ C hC hf)
  have hq : qSequence q = hilbertSequence f :=
    qSequence_encodeQ _ _ (hilbertSequence_zero f)
  have hto : toPareto q = f := by
    apply hilbertSequence_injective
    rw [toPareto_sequence, hq]
  have he : toPareto (qOne - q) = hilbertOne - f := by
    change toParetoLinear (qOne - q) = _
    rw [map_sub]
    change toPareto qOne - toPareto q = _
    rw [toPareto_qOne, hto]
  have hnorm := toPareto_norm_sq_le (qOne - q)
  rw [he] at hnorm
  have herror := (periodic_qError_comparison L hL q
    (by simpa only [hq] using hf) (by simpa only [hq] using hp)).2
  rw [hq] at herror
  exact hnorm.trans (mul_le_mul_of_nonneg_left herror zetaTwo_pos.le)

/-- Finite reciprocal-square tail after the prescribed exact head. -/
def crtTailEnergy (M L : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc (M + 1) L, |1 - F a| ^ 2 / (a : ℝ) ^ 2

theorem crtTailEnergy_nonneg (M L : ℕ) (F : ℕ → ℝ) :
    0 ≤ crtTailEnergy M L F := by
  unfold crtTailEnergy
  exact Finset.sum_nonneg (fun a _ => div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- A zero has an exact nonzero Mellin pairing with every legal residual. -/
theorem normalizedResidue_exact_head_residual_power_lower
    {f : ThresholdHilbert} (hf : f ∈ normalizedResidueSpan)
    (M : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ M → hilbertSequence f k = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ((2 * s.re - 1) / ‖s‖ ^ 2) *
      ((M : ℝ) + 1) ^ (2 * s.re - 1) ≤ ‖hilbertOne - f‖ ^ 2 := by
  have heval := paretoMellin_normalizedResidue_error_identity
    s hs hs1 hz f (subset_closure hf)
  have hehead : ∀ k, 0 < k → k < M + 1 →
      hilbertSequence (hilbertOne - f) k = 0 := by
    intro k hk hkn
    change hilbertSequenceLinear (hilbertOne - f) k = 0
    rw [map_sub]
    change hilbertSequence hilbertOne k - hilbertSequence f k = 0
    rw [hilbertOne_sequence, hhead k hk (by omega)]
    simp [zeroAnchor, ne_of_gt hk]
  have h := mellin_zero_head_lower (hilbertOne - f) (M + 1)
    (by omega) hehead s hs
  rw [heval, norm_div, norm_one, div_pow, one_pow] at h
  convert h using 1 <;> push_cast <;> ring

/-- An off-critical zero forces an explicit positive power of the head length
in every exact-head CRT tail. No squarefreeness is needed for this obstruction. -/
theorem crtTailEnergy_power_lower_of_zeta_zero
    (M L : ℕ) (F : ℕ → ℝ) (hL : 0 < L)
    (hF : F ∈ divisorResidueSpan L)
    (hhead : ∀ n, 0 < n → n ≤ M → F n = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ((2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2)) *
      ((M : ℝ) + 1) ^ (2 * s.re - 1) ≤ crtTailEnergy M L F := by
  obtain ⟨f, hf, hseq, ⟨C, hC⟩, hp⟩ := divisorResidueSpan_lift hF
  have hlo := normalizedResidue_exact_head_residual_power_lower hf M
    (by simpa only [hseq] using hhead) s hs hs1 hz
  have hup := periodic_error_le_zetaTwo_mul_reciprocalEnergy L hL f
    (by simpa only [hseq] using hC) (by simpa only [hseq] using hp)
  rw [hseq, crtReciprocalEnergy_eq_Icc_tail M L _
    (by intro n hn hnM; rw [hhead n hn hnM]; ring)] at hup
  have h := hlo.trans hup
  have hh : (((2 * s.re - 1) / ‖s‖ ^ 2) *
      ((M : ℝ) + 1) ^ (2 * s.re - 1)) / zetaTwo ≤ crtTailEnergy M L F :=
    (div_le_iff₀ zetaTwo_pos).mpr (by simpa only [crtTailEnergy, mul_comm] using h)
  convert hh using 1 <;> simp [div_eq_mul_inv] <;> ring

end RiemannResearch.RH.Pareto
