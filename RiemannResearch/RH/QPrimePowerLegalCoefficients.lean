/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeLegalBasis
import RiemannResearch.RH.QResidueThreeMoments
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.QParityBasis
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import RiemannResearch.RH.QPrimePowerParityBasis

/-!
# Complete-Q coefficients of logarithmic targets in the legal five-vector frame

Source: user-provided legal-basis continuation, 21 October 2026.
All coefficients use summable infinite weighted series; the head-tail identity
retains the full tail. The remaining energy is positive at this finite stage.
No infinite Parseval saturation or RH claim is made.
-/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace RiemannResearch.RH.QPrimePowerLegalCoefficients
open ZetaTwoHilbert ZetaTwoParitySignal PrimePowerTarget QSquarefreeLegalBasis
open ArithmeticCumulative

/-- Complete weighted mean; the zero weight anchors the auxiliary coordinate. -/
def targetMean (p : ℕ) : ℝ :=
  ∑' n : ℕ, positiveQWeight n * (Nat.log p n : ℝ)

def targetEnergy (p : ℕ) : ℝ :=
  ∑' n : ℕ, positiveQWeight n * (Nat.log p n : ℝ) ^ 2

/-- Every positive-integer term is retained, including the infinite tail. -/
def residueMoment (p d : ℕ) : ℝ :=
  ∑' n : ℕ, positiveQWeight n * (Nat.log p n : ℝ) * residueFraction d n

theorem qTarget_mean (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) qOne = targetMean p := by
  rw [qInner_one_tsum, qTarget_sequence]
  rfl

theorem qTarget_energy (p : ℕ) (hp : 1 < p) :
    ‖qTarget p hp‖ ^ 2 = targetEnergy p := by
  rw [qNorm_weighted_sq, qTarget_sequence]
  rfl

theorem qTarget_residueMoment (p d : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) (qResidue d) = residueMoment p d := by
  rw [qInner_weighted, qTarget_sequence, qSequence_qResidue]
  rfl

theorem residueMoment_summable (p d : ℕ) (hp : 1 < p) :
    Summable (fun n : ℕ =>
      positiveQWeight n * (Nat.log p n : ℝ) * residueFraction d n) := by
  simpa only [qTarget_sequence, qSequence_qResidue] using
    qSequence_product_summable (qTarget p hp) (qResidue d)

/-- An exact head-plus-tail formula, never a truncated definition of a coefficient. -/
theorem residueMoment_head_tail (p d N : ℕ) (hp : 1 < p) :
    residueMoment p d =
      (∑ n ∈ Finset.range N,
        positiveQWeight n * (Nat.log p n : ℝ) * residueFraction d n) +
      ∑' k : ℕ, positiveQWeight (k + N) * (Nat.log p (k + N) : ℝ) *
        residueFraction d (k + N) := by
  exact (Summable.sum_add_tsum_nat_add N (residueMoment_summable p d hp)).symm

def parityMoment (p : ℕ) : ℝ :=
  (3 * targetMean p - 8 * residueMoment p 2) / Real.sqrt 3

theorem qTarget_parityMoment (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) parityUnit = parityMoment p := by
  simp only [parityUnit, parityCentered, qEven, qOdd, inner_sub_right,
    real_inner_smul_right, qTarget_mean, qTarget_residueMoment, parityMoment]
  ring

def coefficient3 (p : ℕ) : ℝ :=
  (residueMoment p 3 - inner ℝ (qResidue 3) qOne * targetMean p -
    inner ℝ (qResidue 3) parityUnit * parityMoment p) / ‖remainder3‖

def coefficient5 (p : ℕ) : ℝ :=
  (residueMoment p 5 - inner ℝ (qResidue 5) qOne * targetMean p -
    inner ℝ (qResidue 5) parityUnit * parityMoment p -
    inner ℝ (qResidue 5) unit3 * coefficient3 p) / ‖remainder5‖

def coefficient6 (p : ℕ) : ℝ :=
  (residueMoment p 6 - inner ℝ (qResidue 6) qOne * targetMean p -
    inner ℝ (qResidue 6) parityUnit * parityMoment p -
    inner ℝ (qResidue 6) unit3 * coefficient3 p -
    inner ℝ (qResidue 6) unit5 * coefficient5 p) / ‖remainder6‖

theorem qTarget_coefficient3 (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) unit3 = coefficient3 p := by
  rw [inner_unit3, qTarget_residueMoment, qTarget_mean, qTarget_parityMoment]
  rfl

theorem qTarget_coefficient5 (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) unit5 = coefficient5 p := by
  rw [inner_unit5, qTarget_residueMoment, qTarget_mean,
    qTarget_parityMoment, qTarget_coefficient3]
  rfl

theorem qTarget_coefficient6 (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) unit6 = coefficient6 p := by
  rw [inner_unit6, qTarget_residueMoment, qTarget_mean,
    qTarget_parityMoment, qTarget_coefficient3, qTarget_coefficient5]
  rfl

/-- Exact complete-Q capture and complete remainder for every logarithmic target. -/
theorem qTarget_five_direction_energy (p : ℕ) (hp : 1 < p) :
    targetEnergy p = targetMean p ^ 2 + parityMoment p ^ 2 +
      coefficient3 p ^ 2 + coefficient5 p ^ 2 + coefficient6 p ^ 2 +
      ‖qTarget p hp - approximation6 (qTarget p hp)‖ ^ 2 := by
  have h := approximation6_energy_exact (qTarget p hp)
  simpa [Fin.sum_univ_succ, legalFrame, qTarget_energy, qTarget_mean,
    qTarget_parityMoment, qTarget_coefficient3, qTarget_coefficient5,
    qTarget_coefficient6, add_assoc] using h

theorem parityMoment_two : parityMoment 2 = 1 / Real.sqrt 3 := by
  rw [← qTarget_parityMoment 2 (by norm_num), qTarget_two_inner_parityUnit]

/-- The exact outstanding energy after the five constructed directions. -/
def remainingEnergy (p : ℕ) : ℝ :=
  targetEnergy p - targetMean p ^ 2 - parityMoment p ^ 2 -
    coefficient3 p ^ 2 - coefficient5 p ^ 2 - coefficient6 p ^ 2

theorem remainingEnergy_eq_norm_sq (p : ℕ) (hp : 1 < p) :
    remainingEnergy p = ‖qTarget p hp - approximation6 (qTarget p hp)‖ ^ 2 := by
  rw [remainingEnergy, qTarget_five_direction_energy p hp]
  ring

theorem remainingEnergy_two_pos : 0 < remainingEnergy 2 := by
  rw [remainingEnergy_eq_norm_sq 2 (by norm_num)]
  exact sq_pos_of_pos (norm_pos_iff.mpr qTarget_two_remainder6_ne_zero)

theorem remainingEnergy_three_pos : 0 < remainingEnergy 3 := by
  rw [remainingEnergy_eq_norm_sq 3 (by norm_num)]
  exact sq_pos_of_pos (norm_pos_iff.mpr qTarget_three_remainder6_ne_zero)

/-- Explicit normalization constant of the first new legal coordinate. -/
theorem remainder3_norm_sq_exact :
    ‖remainder3‖ ^ 2 =
      inner ℝ (qResidue 3) qOne - 16 / 81 -
        (inner ℝ (qResidue 3) qOne) ^ 2 -
        ((8 / 9 - 2 * inner ℝ (qResidue 3) qOne) / Real.sqrt 3) ^ 2 := by
  have h := parityApproximation_energy_exact (qResidue 3)
  rw [qResidue_three_norm_sq_exact, qResidue_three_inner_parity_exact] at h
  change ‖qResidue 3 - parityApproximation (qResidue 3)‖ ^ 2 = _
  linarith

theorem qTarget_coefficient3_closed (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) unit3 =
      (residueMoment p 3 - inner ℝ (qResidue 3) qOne * targetMean p -
        ((8 / 9 - 2 * inner ℝ (qResidue 3) qOne) / Real.sqrt 3) *
          parityMoment p) / ‖remainder3‖ := by
  rw [qTarget_coefficient3, coefficient3, qResidue_three_inner_parity_exact]

end RiemannResearch.RH.QPrimePowerLegalCoefficients
