/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDifferenceGram
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.QPrimorialRegularization
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.QPhysicalDifference
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.SquarefreeStageExhaustion
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QPeriod210Certificate
import RiemannResearch.Analysis.PrimitiveRegularization
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A signed prime-eleven improvement of the period-210 certificate

Source: the user-requested signed affine correction investigation, 18 October 2026.
The finite mixed sums are exact rational computations. Their entire infinite
tails are bounded using QFiniteEnergyBounds. The result is a finite certificate
at the same positive penalty; no vanishing-penalty family is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPeriod210AffineCorrection
open ZetaTwoHilbert ZetaTwoProbability QPhysicalDifference QDifferenceGram
open QFiniteEnergyBounds QPeriod210Certificate QPrimorialRegularization
open QSquarefreePrimorialCofinality
open RiemannResearch.Analysis.PrimitiveRegularization

def primeElevenValue (n : ℕ) : ℚ := ((n%11 : ℕ) : ℚ)/11

theorem primeEleven_sequence (n : ℕ) :
    qSequence (qResidue 11) n = (primeElevenValue n : ℝ) := by
  rw [qSequence_qResidue]
  simp [primeElevenValue, ArithmeticCumulative.residueFraction]

theorem primeEleven_abs_le (n : ℕ) : |qSequence (qResidue 11) n| ≤ 10/11 := by
  rw [qSequence_qResidue]
  unfold ArithmeticCumulative.residueFraction
  rw [abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have h := Nat.mod_lt n (by decide : 0 < 11)
  exact_mod_cast (show n%11 ≤ 10 by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel evaluation of the signed first-period mixed sum.
theorem rational_cross_head :
    (∑ n ∈ Finset.range 210, rationalValue (n+1)*primeElevenValue (n+1)/(n+1 : ℚ)^2)
      < 29/200 := by decide +kernel

theorem cross_head_bound :
    (∑ n ∈ Finset.range 210, qSequence candidate (n+1)*
      qSequence (qResidue 11) (n+1)/(n+1 : ℝ)^2) < 29/200 := by
  have h : (((∑ n ∈ Finset.range 210,
      rationalValue (n+1)*primeElevenValue (n+1)/(n+1 : ℚ)^2) : ℚ) : ℝ) <
        (((29 : ℚ)/200) : ℝ) := by exact_mod_cast rational_cross_head
  push_cast at h
  simpa only [candidate_sequence, primeEleven_sequence] using h

theorem cross_inner_bound : inner ℝ candidate (qResidue 11) <
    (76/125 : ℝ)*(29/200+(7/6)*(10/11)/210) := by
  have h := inner_le_head_tail candidate (qResidue 11) 210 (by norm_num)
    (7/6) (10/11) (by norm_num) (by norm_num) candidate_abs_le primeEleven_abs_le
  have hh : (∑ n ∈ Finset.range 210, qSequence candidate (n+1)*
      qSequence (qResidue 11) (n+1)/(n+1 : ℝ)^2) + (7/6)*(10/11)/210 <
        29/200+(7/6)*(10/11)/210 := by linarith [cross_head_bound]
  have hp : 0 < 1/zetaTwo := one_div_pos.mpr zetaTwo_pos
  have h1 := h.trans_lt (mul_lt_mul_of_pos_left hh hp)
  exact h1.trans (mul_lt_mul_of_pos_right inverse_zetaTwo_rational_bounds.2
    (by norm_num : (0 : ℝ) < 29/200+(7/6)*(10/11)/210))

set_option maxRecDepth 100000 in
theorem rational_prime_head :
    (∑ n ∈ Finset.range 210, primeElevenValue (n+1)^2/(n+1 : ℚ)^2) < 103/1000 := by
  decide +kernel

theorem prime_head_bound :
    (∑ n ∈ Finset.range 210, (qSequence (qResidue 11) (n+1))^2/(n+1 : ℝ)^2) <
      103/1000 := by
  have h : (((∑ n ∈ Finset.range 210, primeElevenValue (n+1)^2/(n+1 : ℚ)^2) : ℚ) : ℝ)
      < (((103 : ℚ)/1000) : ℝ) := by exact_mod_cast rational_prime_head
  push_cast at h
  simpa only [primeEleven_sequence] using h

theorem prime_norm_bound : ‖qResidue 11‖^2 <
    (76/125 : ℝ)*(103/1000+(10/11)^2/210) := by
  have h := norm_sq_le_head_tail (qResidue 11) 210 (by norm_num) (10/11)
    (by norm_num) primeEleven_abs_le
  have hh : (∑ n ∈ Finset.range 210, (qSequence (qResidue 11) (n+1))^2/(n+1 : ℝ)^2) +
      (10/11)^2/210 < 103/1000+(10/11)^2/210 := by linarith [prime_head_bound]
  have hp : 0 < 1/zetaTwo := one_div_pos.mpr zetaTwo_pos
  have h1 := h.trans_lt (mul_lt_mul_of_pos_left hh hp)
  exact h1.trans (mul_lt_mul_of_pos_right inverse_zetaTwo_rational_bounds.2
    (by norm_num : (0 : ℝ) < 103/1000+(10/11)^2/210))

theorem derivative_cross_exact :
    inner ℝ (differenceCLM candidate) (differenceCLM (qResidue 11)) =
      103519421/2668050000 := by
  simp only [candidate, map_sum, map_smul, sum_inner, real_inner_smul_left]
  have h : (∑ d ∈ conductors, (coefficientNumerator d : ℝ)/10000 *
      inner ℝ (differenceCLM (qResidue d)) (differenceCLM (qResidue 11))) =
      ∑ d ∈ conductors, (coefficientNumerator d : ℝ)/10000 * derivativeGram d 11 := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [inner_difference_qResidue d 11 (conductor_data d hd).1 (by norm_num)]
  rw [h]
  norm_num [conductors, coefficientNumerator, derivativeGram, Nat.lcm]

theorem prime_derivative_norm : ‖differenceCLM (qResidue 11)‖^2 = 20/1331 := by
  rw [← real_inner_self_eq_norm_sq, inner_difference_qResidue 11 11 (by norm_num) (by norm_num)]
  norm_num [derivativeGram, Nat.lcm]

def curvature : ℝ := ‖differenceCLM (qResidue 11)‖^2 + (1/10)*‖qResidue 11‖^2
def signedGain : ℝ :=
  inner ℝ (differenceCLM qOne-differenceCLM candidate) (differenceCLM (qResidue 11)) -
    (1/10)*inner ℝ candidate (qResidue 11)
def improvedCandidate : QHilbert := candidate + (1/3 : ℝ) • qResidue 11

theorem curvature_pos : 0 < curvature := by
  unfold curvature
  rw [prime_derivative_norm]
  nlinarith [sq_nonneg ‖qResidue 11‖]

theorem curvature_upper : curvature < 188040107/8734687500 := by
  unfold curvature
  rw [prime_derivative_norm]
  nlinarith [prime_norm_bound]

theorem signedGain_lower : (1360133 : ℝ)/185281250 < signedGain := by
  unfold signedGain
  rw [inner_sub_left, inner_difference_qOne_qResidue 11 (by norm_num), derivative_cross_exact]
  have ha := inverse_zetaTwo_rational_bounds.1
  have hc := cross_inner_bound
  nlinarith

theorem improved_mem_stage : improvedCandidate ∈ primorialStage 8 := by
  apply Submodule.add_mem
  · exact primorialStage_mono (by norm_num : 4 ≤ 8) candidate_mem_stage
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨11, by norm_num, ?_, rfl⟩
    have hp : Pareto.SquarefreeStageExhaustion.primorialPeriod 8 = 2310 := by decide +kernel
    rw [hp]
    norm_num

theorem improved_squarefree_legal : improvedCandidate ∈ qSquarefreeCRTSpan :=
  primorialStage_le_squarefreeSpan 8 improved_mem_stage

theorem improved_objective_exact :
    objective (1/10) improvedCandidate = objective (1/10) candidate -
      (2/3)*signedGain + curvature/9 := by
  have h := correction_objective_identity differenceCLM.toLinearMap (differenceCLM qOne)
    (1/10) candidate (qResidue 11) (1/3)
  change curvature*objective (1/10) improvedCandidate =
    curvature*objective (1/10) candidate - signedGain^2 +
      (curvature*(1/3)-signedGain)^2 at h
  have hp := curvature_pos
  have he : curvature*(objective (1/10) improvedCandidate -
      (objective (1/10) candidate-(2/3)*signedGain+curvature/9)) = 0 := by
    nlinarith only [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt hp))

theorem improved_strict_certificate : objective (1/10) improvedCandidate < 469/5000 := by
  rw [improved_objective_exact]
  nlinarith [candidate_strict_certificate, signedGain_lower, curvature_upper]

end RiemannResearch.RH.QPeriod210AffineCorrection
