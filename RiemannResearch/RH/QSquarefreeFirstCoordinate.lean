/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeProjectionSigns
import RiemannResearch.RH.QSquarefreeResidualDivisibility
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QParityConditionalTarget
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A first-coordinate bound for the squarefree target projection

Source: the user-requested analysis of F_infinity(1), 25 October 2026.
The bound is derived here from the existing complete-Q indicator moments,
the physical evaluation vector at one, and Cauchy--Schwarz; no novelty is claimed.
It does not identify the first coordinate with one or determine which side of
one it lies on. No first-coordinate detector from a different projection space
is used.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeFirstCoordinate
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QDivisibilityDensity QDivisorLegality

private theorem firstEvaluation_square_summable :
    Summable (fun n : ℕ => positiveQWeight n *
      (if n = 1 then zetaTwo else 0)^2) := by
  apply boundedQ_square_summable _ zetaTwo zetaTwo_pos.le
  intro n
  by_cases hn : n = 1 <;> simp [hn, abs_of_pos zetaTwo_pos, zetaTwo_pos.le]

/-- The actual Q-Riesz vector for physical evaluation at n=1. -/
def firstEvaluationVector : QHilbert :=
  encodeQ (fun n : ℕ => if n = 1 then zetaTwo else 0) firstEvaluation_square_summable

@[simp] theorem firstEvaluationVector_sequence (n : ℕ) :
    qSequence firstEvaluationVector n = if n = 1 then zetaTwo else 0 := by
  exact congrFun (qSequence_encodeQ _ firstEvaluation_square_summable (by norm_num)) n

theorem inner_firstEvaluationVector (f : QHilbert) :
    inner ℝ f firstEvaluationVector = qSequence f 1 := by
  rw [qInner_weighted]
  calc
    _ = positiveQWeight 1 * qSequence f 1 * qSequence firstEvaluationVector 1 := by
      apply tsum_eq_single 1
      intro n hn
      simp [firstEvaluationVector_sequence, hn]
    _ = _ := by
      simp only [firstEvaluationVector_sequence]
      norm_num [positiveQWeight]
      field_simp [ne_of_gt zetaTwo_pos]

theorem firstEvaluationVector_norm_sq : ‖firstEvaluationVector‖^2 = zetaTwo := by
  rw [← real_inner_self_eq_norm_sq, inner_firstEvaluationVector,
    firstEvaluationVector_sequence]
  norm_num

private def oddVector : QHilbert := (2 : ℝ) • qResidue 2

private theorem oddVector_eq : oddVector = qOne - qDivisor 2 := by
  rw [qDivisor_two_eq]
  unfold oddVector
  abel

private theorem oddVector_first : qSequence oddVector 1 = 1 := by
  change qSequenceLinear ((2 : ℝ) • qResidue 2) 1 = 1
  rw [map_smul]
  change 2 * qSequence (qResidue 2) 1 = 1
  rw [qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

private theorem oddVector_norm_sq : ‖oddVector‖^2 = (3 / 4 : ℝ) := by
  have heo : inner ℝ qOne (qDivisor 2) = (1 / 4 : ℝ) := by
    rw [qOne_inner_qDivisor 2 (by decide)]
    norm_num
  have hoe : inner ℝ (qDivisor 2) qOne = (1 / 4 : ℝ) := by
    rw [real_inner_comm]
    exact heo
  rw [oddVector_eq, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
    qOne_norm_sq, qDivisor_norm_sq 2 (by decide), heo, hoe]
  norm_num

private theorem even_odd_inner : inner ℝ (qDivisor 2) oddVector = 0 := by
  unfold oddVector
  rw [real_inner_smul_right, real_inner_comm]
  rw [qResidue_inner_qDivisor_eq_zero 2 2 (by decide) (dvd_refl _)]
  ring

private theorem residual_odd_inner : inner ℝ limitingResidual oddVector = 0 := by
  unfold oddVector
  rw [real_inner_smul_right]
  have h := Submodule.starProjection_inner_eq_zero qOne (qResidue 2)
    QParityConditionalTarget.qResidue_two_mem_closure
  change inner ℝ limitingResidual (qResidue 2) = 0 at h
  rw [h, mul_zero]

/-- The sharper bound preserves the odd-mean constraint at the first coordinate. -/
theorem projection_first_sq_bound :
    (qSequence (closure.starProjection qOne) 1 - 1)^2 ≤
      (zetaTwo - 4 / 3) / 16 := by
  let v : QHilbert := (1 / 2 : ℝ) • qDivisor 2 - limitingResidual
  let k : QHilbert := firstEvaluationVector - (4 / 3 : ℝ) • oddVector
  have hrev : inner ℝ (qDivisor 2) limitingResidual = ‖limitingResidual‖^2 := by
    rw [real_inner_comm, QSquarefreeResidualDivisibility.residual_even_moment]
  have hvnorm : ‖v‖^2 = (1 / 16 : ℝ) := by
    change ‖(1 / 2 : ℝ) • qDivisor 2 - limitingResidual‖^2 = _
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    rw [qDivisor_norm_sq 2 (by decide)]
    nlinarith [QSquarefreeResidualDivisibility.residual_even_moment, hrev]
  have hvodd : inner ℝ v oddVector = 0 := by
    change inner ℝ ((1 / 2 : ℝ) • qDivisor 2 - limitingResidual) oddVector = 0
    rw [inner_sub_left, real_inner_smul_left, even_odd_inner, residual_odd_inner]
    ring
  have hfirst : inner ℝ firstEvaluationVector oddVector = 1 := by
    rw [real_inner_comm, inner_firstEvaluationVector, oddVector_first]
  have hfirst' : inner ℝ oddVector firstEvaluationVector = 1 := by
    rw [inner_firstEvaluationVector, oddVector_first]
  have hknorm : ‖k‖^2 = zetaTwo - 4 / 3 := by
    change ‖firstEvaluationVector - (4 / 3 : ℝ) • oddVector‖^2 = _
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    rw [firstEvaluationVector_norm_sq, oddVector_norm_sq]
    nlinarith [hfirst, hfirst']
  have hvfirst : qSequence v 1 = qSequence (closure.starProjection qOne) 1 - 1 := by
    change qSequenceLinear ((1 / 2 : ℝ) • qDivisor 2 - limitingResidual) 1 = _
    rw [map_sub, map_smul]
    change (1 / 2 : ℝ) * qSequence (qDivisor 2) 1 - qSequence limitingResidual 1 = _
    rw [QSquarefreeProjectionSigns.limitingResidual_sequence 1 (by decide),
      qSequence_qDivisor]
    norm_num [positiveDivisor]
  have hvk : inner ℝ v k = qSequence (closure.starProjection qOne) 1 - 1 := by
    change inner ℝ v (firstEvaluationVector - (4 / 3 : ℝ) • oddVector) = _
    rw [inner_sub_right, real_inner_smul_right, hvodd, mul_zero, sub_zero,
      inner_firstEvaluationVector, hvfirst]
  have hcs := abs_real_inner_le_norm v k
  have hs := mul_self_le_mul_self (abs_nonneg (inner ℝ v k)) hcs
  have hs' : (inner ℝ v k)^2 ≤ ‖v‖^2 * ‖k‖^2 := by
    simpa only [← pow_two, sq_abs, mul_pow] using hs
  rw [hvk, hvnorm, hknorm] at hs'
  nlinarith

end RiemannResearch.RH.QSquarefreeFirstCoordinate
