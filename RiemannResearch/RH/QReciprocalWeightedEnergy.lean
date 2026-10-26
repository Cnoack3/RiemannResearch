/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QShiftedReciprocalTail
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.Analysis.PolylogAbelBudget
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A small complete weighted budget for the raw reciprocal source

Source: the user's missing squarefree cross-moment bound request,
26 October 2026. These unconditional multiplier estimates precede projection;
they do not assert weighted stability of the legal projection.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QShiftedReciprocal
open ZetaTwoHilbert QAnnihilatorTailEscape QPolylogTailEnergy
open RiemannResearch.Analysis.LogTailWeights

theorem reciprocal_weightedEnergyTerm_le (f : QHilbert) (n : ℕ) :
    polylogWeightedEnergyTerm 2 (B f) n ≤
      (1 / 256 : ℝ) * (positiveQWeight n * qSequence f n ^ 2) := by
  have h := mul_le_mul_of_nonneg_right (polylog_two_reciprocal_multiplier_le n)
    (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg (qSequence f n)))
  simp only [polylogWeightedEnergyTerm, qSequence_B, div_pow]
  calc
    polylogTailProfile 2 n * positiveQWeight n *
        (qSequence f n ^ 2 / ((n : ℝ) + 1) ^ 2) =
        polylogTailProfile 2 n / ((n : ℝ) + 1) ^ 2 *
          (positiveQWeight n * qSequence f n ^ 2) := by ring
    _ ≤ _ := h

theorem reciprocal_weightedEnergy_summable (f : QHilbert) :
    Summable (polylogWeightedEnergyTerm 2 (B f)) := by
  exact Summable.of_nonneg_of_le (polylogWeightedEnergyTerm_nonneg 2 (B f))
    (reciprocal_weightedEnergyTerm_le f)
    ((qSequence_square_summable f).mul_left (1 / 256 : ℝ))

/-- The complete weighted source costs at most 1/256 of its input Q energy. -/
theorem reciprocal_weightedEnergy_le (f : QHilbert) :
    (∑' n : ℕ, polylogWeightedEnergyTerm 2 (B f) n) ≤ ‖f‖ ^ 2 / 256 := by
  have h := (reciprocal_weightedEnergy_summable f).tsum_le_tsum
    (reciprocal_weightedEnergyTerm_le f)
    ((qSequence_square_summable f).mul_left (1 / 256 : ℝ))
  rw [tsum_mul_left, ← qNorm_weighted_sq] at h
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using h

end RiemannResearch.RH.QShiftedReciprocal
