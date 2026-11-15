/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPeriodicCertifiedWeights
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ParetoResidueMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.ReciprocalProgressionCertificates
import RiemannResearch.Analysis.LogRationalCertificates
import RiemannResearch.RH.QResidueFirstNormalization
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ParetoProgressionCalculus
import RiemannResearch.RH.ZetaTwoElementaryRationalBounds
import Mathlib.Analysis.SumOverResidueClass

/-!
# The exact binary reciprocal interpolation example

Source: Reciprocal_Head_Investigation_2026-11-07.md, Section 4.
The target is the actual shifted reciprocal image of the legal atom g₂.
Complete norms and inner products include the entire physical sequence.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QBinaryReciprocalExample
open ZetaTwoHilbert ZetaTwoProbability QResidueFirstNormalization
open RiemannResearch.Analysis.ParetoProgressionCertificates

/-- The actual legal-atom target Rg₂. The repository's legacy operator name is B. -/
def target : QHilbert := QShiftedReciprocal.B (qResidue 2)

/-- The complete one-dimensional projection coefficient. -/
def projectionCoefficient : ℝ := 1 - 4*Real.log 2/(3*zetaTwo)

private theorem tsum_odd {f : ℕ → ℝ} (hf : Summable f)
    (heven : ∀ n, f (2*n) = 0) :
    (∑' k : ℕ, f k) = ∑' n : ℕ, f (2*n+1) := by
  have h : (∑' k : ℕ, f k) =
      ∑ r : Fin 2, ∑' n : ℕ, f (r.val + 2 * n) :=
    Nat.sumByResidueClasses hf 2
  simpa [Fin.sum_univ_succ, heven, add_comm] using h

/-- The complete binary Q Gram entry. -/
theorem gram : inner ℝ (qResidue 2) (qResidue 2) = (3/16 : ℝ) := by
  rw [real_inner_self_eq_norm_sq, qResidue_two_norm_sq]

private theorem pareto_gram :
    inner ℝ (ZetaTwoParetoTransfer.toPareto (qResidue 2))
      (ZetaTwoParetoTransfer.toPareto (qResidue 2)) = Real.log 2/4 := by
  rw [Pareto.hilbert_inner_weighted, ZetaTwoParetoTransfer.toPareto_sequence,
    qSequence_qResidue]
  have he : (fun k : ℕ => Pareto.positiveWeight k *
      (ArithmeticCumulative.residueFraction 2 k * ArithmeticCumulative.residueFraction 2 k)) =
      fun k : ℕ => (1/4 : ℝ) * (Pareto.positiveWeight k *
        (Pareto.residue 2 k * Pareto.residue 2 k)) := by
    funext k
    unfold ArithmeticCumulative.residueFraction Pareto.residue
    norm_num
    ring
  unfold Pareto.paretoInner
  rw [he, tsum_mul_left]
  change (1/4 : ℝ)*Pareto.paretoInner (Pareto.residue 2) (Pareto.residue 2) = _
  rw [Pareto.paretoInner_residue_two]
  ring

/-- Exact pairing with the full reciprocal target. -/
theorem target_inner : inner ℝ (qResidue 2) target =
    (3/16 : ℝ) - Real.log 2/(4*zetaTwo) := by
  have h := QShiftedReciprocal.pareto_inner_identity (qResidue 2) (qResidue 2)
  rw [pareto_gram, gram] at h
  change Real.log 2/4 = zetaTwo*((3/16 : ℝ)-inner ℝ (qResidue 2) target) at h
  apply (eq_sub_iff_add_eq).mpr
  apply (mul_right_cancel₀ (ne_of_gt zetaTwo_pos))
  field_simp [ne_of_gt zetaTwo_pos] at h ⊢
  nlinarith [h]

private theorem raw_odd_weight : rawResidueSquareWeight 2 1 = 3*zetaTwo/4 := by
  have hg := qResidue_two_norm_sq
  rw [qNorm_weighted_sq] at hg
  rw [tsum_odd (qSequence_square_summable (qResidue 2)) (by
    intro n
    simp [qSequence_qResidue, ArithmeticCumulative.residueFraction, Nat.mul_mod])] at hg
  have he (n : ℕ) : positiveQWeight (2*n+1) *
      (qSequence (qResidue 2) (2*n+1))^2 =
      (1/(4*zetaTwo))*(1/(1+(n:ℝ)*2)^2) := by
    rw [qSequence_qResidue]
    norm_num [ArithmeticCumulative.residueFraction, positiveQWeight,
      Nat.add_mod, Nat.mul_mod]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  simp_rw [he] at hg
  rw [tsum_mul_left] at hg
  change (1/(4*zetaTwo))*rawResidueSquareWeight 2 1 = 3/16 at hg
  field_simp [ne_of_gt zetaTwo_pos] at hg
  nlinarith

private theorem raw_even_weight : rawResidueSquareWeight 2 2 = zetaTwo/4 := by
  calc
    rawResidueSquareWeight 2 2 = (1/4 : ℝ)*rawResidueSquareWeight 1 1 := by
      unfold rawResidueSquareWeight
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      have hn : 0 < 1+(n:ℝ) := by positivity
      have hn' : 0 < 2+(n:ℝ)*2 := by positivity
      field_simp [ne_of_gt hn, ne_of_gt hn']
      <;> ring
    _ = zetaTwo/4 := by rw [rawResidueSquareWeight_one_one]; ring

private theorem pareto_odd_weight : paretoProgression 1 2 = Real.log 2 := by
  rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    paretoProgression_eq_progressionWeight]
  exact Pareto.progressionWeight_two_one

private theorem reciprocal_odd_weight :
    reciprocalProgression 1 2 = zetaTwo - 2*Real.log 2 := by
  rw [reciprocalProgression_eq_raw_signed 1 2 (by norm_num) (by norm_num)]
  norm_num only [show (1 : ℝ)+1=2 by norm_num]
  rw [raw_odd_weight, raw_even_weight, pareto_odd_weight]
  ring

/-- Exact complete norm of the reciprocal target. -/
theorem target_norm_sq : ‖target‖^2 = (1/4 : ℝ) - Real.log 2/(2*zetaTwo) := by
  rw [qNorm_weighted_sq]
  rw [tsum_odd (qSequence_square_summable target) (by
    intro n
    simp [target, QShiftedReciprocal.qSequence_B, qSequence_qResidue,
      ArithmeticCumulative.residueFraction, Nat.mul_mod])]
  have he (n : ℕ) : positiveQWeight (2*n+1) * (qSequence target (2*n+1))^2 =
      (1/(4*zetaTwo)) *
        (1/((1+2*(n:ℝ))^2*(1+2*(n:ℝ)+1)^2)) := by
    simp only [target, QShiftedReciprocal.qSequence_B, qSequence_qResidue]
    norm_num [ArithmeticCumulative.residueFraction, positiveQWeight,
      Nat.add_mod, Nat.mul_mod]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  simp_rw [he]
  rw [tsum_mul_left]
  change (1/(4*zetaTwo))*reciprocalProgression 1 2 = _
  rw [reciprocal_odd_weight]
  field_simp [ne_of_gt zetaTwo_pos]
  <;> ring

/-- Exact full error for every candidate coefficient, before minimization. -/
theorem error_formula (c : ℝ) :
    ‖target-c • qResidue 2‖^2 =
      (1/4 : ℝ) - Real.log 2/(2*zetaTwo) -
        2*c*((3/16 : ℝ)-Real.log 2/(4*zetaTwo)) + (3/16 : ℝ)*c^2 := by
  have hp : inner ℝ target (qResidue 2) =
      (3/16 : ℝ)-Real.log 2/(4*zetaTwo) := (real_inner_comm _ _).trans target_inner
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    qResidue_two_norm_sq, real_inner_smul_right,
    hp, target_norm_sq]
  ring

/-- The first-head interpolant has this exact complete error. -/
theorem first_head_error_formula :
    ‖target-(1/2 : ℝ) • qResidue 2‖^2 =
      (7/64 : ℝ)-Real.log 2/(4*zetaTwo) := by
  rw [error_formula]
  ring

/-- The unconstrained complete projection error, retaining its exact Gram denominator. -/
theorem projection_error_formula :
    ‖target-projectionCoefficient • qResidue 2‖^2 =
      (1/4 : ℝ)-Real.log 2/(2*zetaTwo) -
        (16/3 : ℝ)*((3/16 : ℝ)-Real.log 2/(4*zetaTwo))^2 := by
  rw [error_formula]
  unfold projectionCoefficient
  field_simp [ne_of_gt zetaTwo_pos]
  <;> ring

/-- The projection coefficient is determined by the complete normal equation. -/
theorem projection_normal_equation :
    inner ℝ (qResidue 2) (target - projectionCoefficient • qResidue 2) = 0 := by
  rw [inner_sub_right, real_inner_smul_right, target_inner, gram]
  unfold projectionCoefficient
  field_simp [ne_of_gt zetaTwo_pos]
  <;> ring

/-- The exact positive error cost of changing the full projection coefficient. -/
theorem error_completion (c : ℝ) :
    ‖target-c • qResidue 2‖^2 =
      ‖target-projectionCoefficient • qResidue 2‖^2 +
        (3/16 : ℝ)*(c-projectionCoefficient)^2 := by
  have hp : inner ℝ target (qResidue 2) =
      (3/16 : ℝ)-Real.log 2/(4*zetaTwo) := (real_inner_comm _ _).trans target_inner
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
    qResidue_two_norm_sq, real_inner_smul_right, real_inner_smul_right,
    hp]
  unfold projectionCoefficient
  field_simp [ne_of_gt zetaTwo_pos]
  <;> ring

/-- The complete projection minimizes the full Q error within span(g₂). -/
theorem projection_minimal (c : ℝ) :
    ‖target-projectionCoefficient • qResidue 2‖^2 ≤ ‖target-c • qResidue 2‖^2 := by
  rw [error_completion c]
  nlinarith [sq_nonneg (c-projectionCoefficient)]

/-- Exact interpolation at the first physical head forces coefficient 1/2. -/
theorem first_head_iff (c : ℝ) :
    qSequence (c • qResidue 2) 1 = qSequence target 1 ↔ c = (1/2 : ℝ) := by
  change (qSequenceLinear (c • qResidue 2)) 1 = _ ↔ _
  rw [map_smul]
  change c*qSequence (qResidue 2) 1 = qSequence target 1 ↔ _
  simp only [target, QShiftedReciprocal.qSequence_B, qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]
  constructor <;> intro h <;> linarith

private theorem log_two_ge_two_thirds : (2/3 : ℝ) ≤ Real.log 2 := by
  have h := RiemannResearch.Analysis.LogRationalCertificates.logOnePlusInvInterval_contains
    (1 : ℚ) (by norm_num) 1
  norm_num [RiemannResearch.Analysis.LogRationalCertificates.logOnePlusInvInterval,
    RiemannResearch.RatInterval.Contains, Finset.sum_range_succ] at h
  exact h.1

/-- The full projection misses the first head: its coefficient is strictly below 1/2. -/
theorem projectionCoefficient_lt_half : projectionCoefficient < (1/2 : ℝ) := by
  have hlog := log_two_ge_two_thirds
  have hZ := zetaTwo_lt_five_thirds
  have hpos : 0 < 3*zetaTwo := mul_pos (by norm_num) zetaTwo_pos
  have hd : (1/2 : ℝ) < 4*Real.log 2/(3*zetaTwo) :=
    (lt_div_iff₀ hpos).2 (by nlinarith)
  unfold projectionCoefficient
  linarith

/-- The exact interpolation cost is strictly positive. -/
theorem first_head_extra_cost_pos :
    0 < (3/16 : ℝ)*((1/2 : ℝ)-projectionCoefficient)^2 := by
  exact mul_pos (by norm_num) (sq_pos_of_pos (sub_pos.mpr projectionCoefficient_lt_half))

theorem first_head_error_strict :
    ‖target-projectionCoefficient • qResidue 2‖^2 <
      ‖target-(1/2 : ℝ) • qResidue 2‖^2 := by
  rw [error_completion (1/2 : ℝ)]
  linarith [first_head_extra_cost_pos]

end RiemannResearch.RH.QBinaryReciprocalExample
