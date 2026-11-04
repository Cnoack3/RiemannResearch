/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QBasisDPPBridge
import RiemannResearch.RH.QDivisorModeLegality
import RiemannResearch.RH.QSquarefreeJumpDistance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A two-witness improvement for squarefree DPP mode three

Source: the user's request to improve proved basis and DPP bounds,
4 November 2026. Two explicit four-site witnesses from
QSquarefreeJumpDistance are combined with their complete cross term.
Their coefficients come from the inverse of the 2x2 witness Gram matrix.
The resulting constant is stronger than the one-witness certificate.
It is an obstruction at ambient divisor mode 3, not a lower bound for
the constant-mode vacancy and not an RH disproof.
-/

noncomputable section
open MeasureTheory
open RiemannResearch.RH
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QDivisorHilbert
open QSquarefreeJumpDistance SquarefreeRadicalDifference ArithmeticCumulative
open QDivisorProjectionDPP QBasisDPPBridge

namespace RiemannResearch.RH.QDivisorModeVacancyImprovement

theorem witness_two_five_inner :
    inner ℝ (squareJumpWitness 2) (squareJumpWitness 5) = 16 * zetaTwo := by
  rw [squareJumpWitness_inner 2 (by decide)]
  simp only [qDifference]
  have hadd (x y : QHilbert) (n : ℕ) :
      qSequence (x + y) n = qSequence x n + qSequence y n :=
    congrFun (qSequenceLinear.map_add x y) n
  have hsub (x y : QHilbert) (n : ℕ) :
      qSequence (x - y) n = qSequence x n - qSequence y n :=
    congrFun (qSequenceLinear.map_sub x y) n
  simp only [squareJumpWitness, hadd, hsub]
  norm_num only [Nat.reducePow, Nat.reduceSub]
  simp only [qSequence_qSiteRiesz 25 (by decide), qSequence_qSiteRiesz 24 (by decide),
    qSequence_qSiteRiesz 5 (by decide), qSequence_qSiteRiesz 4 (by decide)]
  norm_num [positiveQWeight, ne_of_gt zetaTwo_pos]
  ring

theorem divisor_three_jump_five :
    squareJumpFunctional 5 (normalizedDivisorWavelet 3) = -9 / Real.sqrt 8 := by
  have hdiv : squareJumpFunctional 5 (qDivisor 3) = -1 := by
    rw [squareJumpFunctional_apply 5 (by decide)]
    simp only [qDifference, qSequence_qDivisor]
    norm_num [positiveDivisor]
  have hone : squareJumpFunctional 5 qOne = 0 := by
    rw [squareJumpFunctional_apply 5 (by decide)]
    simp only [qDifference, qSequence_qOne]
    norm_num [qOneSequence]
  rw [QDivisorModeLegality.normalizedDivisorWavelet_three_explicit,
    map_smul, map_sub, map_smul, hdiv, hone]
  simp only [smul_eq_mul]
  ring

def pairedJumpWitness : QHilbert :=
  (613 : ℝ) • squareJumpWitness 2 + (7 : ℝ) • squareJumpWitness 5

theorem pairedJumpWitness_norm_sq :
    ‖pairedJumpWitness‖ ^ 2 = 11471240 * zetaTwo := by
  rw [pairedJumpWitness, norm_add_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right, witness_two_five_inner]
  simp only [mul_pow]
  rw [squareJumpWitness_norm_sq 2 (by decide),
    squareJumpWitness_norm_sq 5 (by decide)]
  norm_num [Real.norm_eq_abs]
  ring

theorem pairedJumpWitness_three :
    inner ℝ pairedJumpWitness (normalizedDivisorWavelet 3) = -5580 / Real.sqrt 8 := by
  rw [pairedJumpWitness, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  change 613 * squareJumpFunctional 2 (normalizedDivisorWavelet 3) +
      7 * squareJumpFunctional 5 (normalizedDivisorWavelet 3) = _
  rw [QDivisorModeLegality.divisor_mode_three_squareJump, divisor_three_jump_five]
  ring

theorem pairedJumpWitness_legal (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    inner ℝ pairedJumpWitness F = 0 := by
  rw [pairedJumpWitness, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    squareJumpWitness_inner_eq_zero 2 (by decide) F hF,
    squareJumpWitness_inner_eq_zero 5 (by decide) F hF]
  ring

theorem pairedJumpWitness_bound (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    12555 / (37004 * zetaTwo) ≤ ‖normalizedDivisorWavelet 3 - F‖ ^ 2 := by
  have h := real_inner_mul_inner_self_le pairedJumpWitness (normalizedDivisorWavelet 3 - F)
  rw [inner_sub_right, pairedJumpWitness_three, pairedJumpWitness_legal F hF,
    sub_zero, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    pairedJumpWitness_norm_sq] at h
  have hs : Real.sqrt (8 : ℝ) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hv : (-5580 / Real.sqrt (8 : ℝ)) * (-5580 / Real.sqrt (8 : ℝ)) =
      3892050 := by
    rw [← pow_two, div_pow, neg_sq, hs]
    norm_num
  rw [hv] at h
  apply (div_le_iff₀ (mul_pos (by norm_num) zetaTwo_pos)).mpr
  nlinarith

theorem squarefree_mode_three_vacancy_improved (n : ℕ) :
    12555 / (37004 * zetaTwo) ≤
      (modeLaw (ZetaTwoOptimizerStage.stage n)).real {x | x 3 = false} := by
  rw [QDivisorProjectionDPP.modeLaw_vacancy_energy]
  apply pairedJumpWitness_bound
  exact qSquarefreeCRTSpan.le_topologicalClosure
    (squarefree_stage_le_arithmetic_span n
      ((ZetaTwoOptimizerStage.stage n).starProjection_apply_mem _))

/-- The two-witness rational constant strictly improves the one-witness bound. -/
theorem paired_bound_strictly_improves :
    (27 / 80 : ℝ) < 12555 / 37004 := by norm_num

end RiemannResearch.RH.QDivisorModeVacancyImprovement
