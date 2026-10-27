/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalPairCorrection
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# The actual mixed-conductor family in the Q Hilbert space

Source: LegalSubspaceProjectionObstruction.md. These definitions use the full
inverse-square measure and the actual residual of the specified subspace.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QLegalMixedConductor
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QDivisorLegality QDivisibilityDensity QShiftedReciprocal
open RiemannResearch.Analysis.OrthogonalPairCorrection

abbrev parityAtom : QHilbert := qResidue 2
abbrev evenTarget : QHilbert := qDivisor 2

theorem parityAtom_inner_evenTarget : inner ℝ parityAtom evenTarget = 0 :=
  qResidue_inner_qDivisor_eq_zero 2 2 (by norm_num) (dvd_refl _)

theorem evenTarget_inner_parityAtom : inner ℝ evenTarget parityAtom = 0 := by
  rw [real_inner_comm]; exact parityAtom_inner_evenTarget

theorem qOne_eq_parity_even : qOne = (2 : ℝ) • parityAtom + evenTarget := by
  change qOne = (2 : ℝ) • parityAtom + qDivisor 2
  rw [qDivisor_two_eq]; abel

theorem qOne_inner_parityAtom : inner ℝ qOne parityAtom = 3 / 8 := by
  have h := qOne_inner_qDivisor 2 (by norm_num)
  rw [qDivisor_two_eq, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, qOne_norm_sq] at h
  norm_num at h ⊢
  linarith

theorem parityAtom_norm_sq : ‖parityAtom‖ ^ 2 = 3 / 16 := by
  have h := parityAtom_inner_evenTarget
  change inner ℝ parityAtom (qDivisor 2) = 0 at h
  have hsym : inner ℝ parityAtom qOne = 3 / 8 := by
    rw [real_inner_comm]
    exact qOne_inner_parityAtom
  rw [qDivisor_two_eq, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hsym] at h
  linarith

theorem parityAtom_ne_zero : parityAtom ≠ 0 := by
  intro h
  have := parityAtom_norm_sq
  norm_num [h] at this

theorem evenTarget_norm_sq : ‖evenTarget‖ ^ 2 = 1 / 4 := by
  change ‖qDivisor 2‖ ^ 2 = 1 / 4
  have h := qDivisor_norm_sq 2 (by norm_num)
  norm_num at h ⊢
  exact h

/-- The large coefficient multiplies the actual legal residue atom. -/
def highPart (d : ℕ) : QHilbert := (10 * Real.sqrt (d : ℝ)) • qResidue d

def mixedVector (d : ℕ) : QHilbert := qResidue 3 + highPart d

def parityCoefficient (d : ℕ) : ℝ :=
  inner ℝ (mixedVector d) parityAtom / ‖parityAtom‖ ^ 2

def orthogonalVector (d : ℕ) : QHilbert :=
  mixedVector d - parityCoefficient d • parityAtom

def mixedSpace (d : ℕ) : Submodule ℝ QHilbert :=
  pairSpace parityAtom (orthogonalVector d)

instance mixedSpace_finiteDimensional (d : ℕ) : FiniteDimensional ℝ (mixedSpace d) :=
  pairSpace_finiteDimensional _ _

theorem orthogonalVector_orthogonal (d : ℕ) :
    inner ℝ parityAtom (orthogonalVector d) = 0 := by
  rw [real_inner_comm, orthogonalVector, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, parityCoefficient, div_mul_cancel₀]
  · exact sub_self _
  · rw [parityAtom_norm_sq]; norm_num

theorem mixedSpace_eq_span (d : ℕ) :
    mixedSpace d = Submodule.span ℝ ({parityAtom, mixedVector d} : Set QHilbert) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact left_mem_pairSpace _ _
    · have hm : orthogonalVector d + parityCoefficient d • parityAtom ∈ mixedSpace d :=
        (mixedSpace d).add_mem (right_mem_pairSpace _ _)
          ((mixedSpace d).smul_mem _ (left_mem_pairSpace _ _))
      have he : orthogonalVector d + parityCoefficient d • parityAtom = mixedVector d := by
        unfold orthogonalVector
        abel
      rw [he] at hm
      exact hm

theorem qSequence_orthogonalVector (d n : ℕ) :
    qSequence (orthogonalVector d) n = residueFraction 3 n +
      10 * Real.sqrt (d : ℝ) * residueFraction d n -
      parityCoefficient d * residueFraction 2 n := by
  change qSequenceLinear (qResidue 3 + (10 * Real.sqrt (d : ℝ)) • qResidue d -
    parityCoefficient d • qResidue 2) n = _
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change qSequence (qResidue 3) n +
      10 * Real.sqrt (d : ℝ) * qSequence (qResidue d) n -
      parityCoefficient d * qSequence (qResidue 2) n = _
  rw [qSequence_qResidue, qSequence_qResidue, qSequence_qResidue]

theorem orthogonalVector_ne_zero (d : ℕ) (hd : 2 < d) : orthogonalVector d ≠ 0 := by
  intro hz
  have h := qSequence_orthogonalVector d 2
  have hz' : qSequence (orthogonalVector d) 2 = 0 := by
    rw [hz]; change qSequenceLinear 0 2 = 0; simp
  rw [hz'] at h
  simp only [residueFraction, Nat.mod_eq_of_lt hd] at h
  norm_num at h
  have hp : 0 ≤ 10 * Real.sqrt (d : ℝ) * (2 / (d : ℝ)) := by positivity
  linarith

def actualResidual (d : ℕ) : QHilbert := qOne - (mixedSpace d).starProjection qOne

def actualCorrection (d : ℕ) : QHilbert :=
  (mixedSpace d).starProjection (B (actualResidual d))

def gram (d : ℕ) : ℝ := ‖orthogonalVector d‖ ^ 2

def targetMoment (d : ℕ) : ℝ := inner ℝ evenTarget (orthogonalVector d)
def sourceMoment (d : ℕ) : ℝ := inner ℝ (orthogonalVector d) (B evenTarget)
def reciprocalMoment (d : ℕ) : ℝ := inner ℝ (orthogonalVector d) (B (orthogonalVector d))

def correctionCoefficient (d : ℕ) : ℝ :=
  (sourceMoment d * gram d - targetMoment d * reciprocalMoment d) / (gram d) ^ 2

def correctionParityCoefficient (d : ℕ) : ℝ :=
  inner ℝ (B (actualResidual d)) parityAtom / ‖parityAtom‖ ^ 2

theorem actualResidual_eq (d : ℕ) (hd : 2 < d) :
    actualResidual d = evenTarget - (targetMoment d / gram d) • orthogonalVector d := by
  unfold actualResidual
  rw [qOne_eq_parity_even]
  exact residual_pair_eq parityAtom (orthogonalVector d) evenTarget 2
    parityAtom_ne_zero (orthogonalVector_ne_zero d hd) (orthogonalVector_orthogonal d)
    evenTarget_inner_parityAtom

theorem actualCorrection_eq (d : ℕ) (hd : 2 < d) :
    actualCorrection d = correctionParityCoefficient d • parityAtom +
      correctionCoefficient d • orthogonalVector d := by
  have h := correction_pair_eq parityAtom (orthogonalVector d) evenTarget 2 B
    parityAtom_ne_zero (orthogonalVector_ne_zero d hd) (orthogonalVector_orthogonal d)
    evenTarget_inner_parityAtom
  rw [← qOne_eq_parity_even] at h
  change actualCorrection d =
    (inner ℝ (B (evenTarget - (targetMoment d / gram d) • orthogonalVector d)) parityAtom /
      ‖parityAtom‖ ^ 2) • parityAtom + correctionCoefficient d • orthogonalVector d at h
  rw [← actualResidual_eq d hd] at h
  exact h

/-- Exact actual physical correction, keeping both signed coefficients. -/
theorem actualCorrection_sequence (d n : ℕ) (hd : 2 < d) :
    qSequence (actualCorrection d) n =
      correctionCoefficient d * (10 * Real.sqrt (d : ℝ)) * residueFraction d n +
      (correctionParityCoefficient d - correctionCoefficient d * parityCoefficient d) *
        residueFraction 2 n + correctionCoefficient d * residueFraction 3 n := by
  rw [actualCorrection_eq d hd]
  change qSequenceLinear (correctionParityCoefficient d • parityAtom +
    correctionCoefficient d • orthogonalVector d) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change correctionParityCoefficient d * qSequence (qResidue 2) n +
    correctionCoefficient d * qSequence (orthogonalVector d) n = _
  rw [qSequence_qResidue, qSequence_orthogonalVector]
  ring

/-- The finite scalar threshold applies to these actual residual coefficients. -/
theorem actualCorrection_coefficient_lower (d : ℕ)
    (hG : 25 ≤ gram d) (hGM : gram d ≤ 303)
    (ha0 : 0 ≤ targetMoment d) (ha : targetMoment d ≤ 1 / 2)
    (hD : 1 / 36 ≤ sourceMoment d) (hE : reciprocalMoment d ≤ 1) :
    7 / (36 * 303 ^ 2 : ℝ) ≤ correctionCoefficient d := by
  exact correction_coefficient_lower _ _ _ _ hG hGM ha0 ha hD
    (B_positive _) hE

end RiemannResearch.RH.QLegalMixedConductor
