/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ResidueDerivativeCompatibility
import RiemannResearch.RH.ResidueDualDifferences
import RiemannResearch.RH.MobiusResidualFirstCoordinate

/-!
# Exact physical rows of the derivative compatibility obstruction

The anchored weighted adjoint retains the ratio n/(n+2). These identities
do not assert that the resulting arithmetic-progression pairing vanishes.

Source: the user-directed vanishing attempt, continuing
`CRTPrimitiveTransferAudit20260929.md`, Section 6, and the existing
repository dyadic and arithmetic identities.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

theorem hilbertBackwardShift_atom (k : ℕ) (hk : 0 < k) :
    hilbertBackwardShift (hilbertAtom k hk) = hilbertAtom (k + 1) (by omega) := by
  apply hilbertSequence_injective
  rw [hilbertBackwardShift_sequence, hilbertAtom_sequence, hilbertAtom_sequence]
  funext n
  simp only [PrimitiveEnergy.backwardShift]
  have he : n - 1 = k ↔ n = k + 1 := by omega
  simp only [he]

theorem hilbertDifference_atom (k : ℕ) (hk : 0 < k) :
    hilbertDifference (hilbertAtom k hk) =
      hilbertAtom k hk - hilbertAtom (k + 1) (by omega) := by
  rw [hilbertDifference_apply, hilbertBackwardShift_atom]

/-- The adjoint of the anchored backward difference, with the exact Pareto ratio. -/
theorem hilbertDifference_adjoint_sequence (f : ThresholdHilbert)
    (k : ℕ) (hk : 0 < k) :
    hilbertSequence (hilbertDifference.adjoint f) k =
      hilbertSequence f k - (k : ℝ) / ((k : ℝ) + 2) * hilbertSequence f (k + 1) := by
  have he := ContinuousLinearMap.adjoint_inner_right
    hilbertDifference (hilbertAtom k hk) f
  rw [hilbertAtom_inner, hilbertDifference_atom, inner_sub_left,
    hilbertAtom_inner, hilbertAtom_inner] at he
  have hratio : positiveWeight (k + 1) =
      positiveWeight k * ((k : ℝ) / ((k : ℝ) + 2)) := by
    unfold positiveWeight
    push_cast
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  have hw : positiveWeight k ≠ 0 := by unfold positiveWeight; positivity
  apply mul_left_cancel₀ hw
  rw [he, hratio]
  ring

namespace CoefficientStabilization.DerivativeCompatibility
open RiemannResearch.RH.ArithmeticCumulative

theorem derivativeAtom_sequence_positive (i k : ℕ) (hk : 0 < k) :
    hilbertSequence (derivativeAtom i) k =
      1 / ((i + 2 : ℕ) : ℝ) - divisorIndicator (i + 2) k := by
  rw [derivativeAtom, hilbertDifference_sequence, residueAtom,
    normalizedResidueHilbert_sequence]
  change residueFraction (i + 2) k - residueFraction (i + 2) (k - 1) = _
  have h := CorrectionTail.residueFraction_forward_eq_divisor
    (i + 2) (k - 1) (by omega)
  simpa only [Nat.sub_add_cancel hk] using h

/-- This is the actual adjoint test, rather than an assumed legal atom. -/
def derivativeAdjointRow (i : ℕ) : ThresholdHilbert :=
  hilbertDifference.adjoint (derivativeAtom i)

theorem derivativeAdjointRow_sequence (i k : ℕ) (hk : 0 < k) :
    hilbertSequence (derivativeAdjointRow i) k =
      2 / (((i + 2 : ℕ) : ℝ) * ((k : ℝ) + 2)) -
        divisorIndicator (i + 2) k +
        (k : ℝ) / ((k : ℝ) + 2) * divisorIndicator (i + 2) (k + 1) := by
  rw [derivativeAdjointRow, hilbertDifference_adjoint_sequence _ k hk,
    derivativeAtom_sequence_positive i k hk,
    derivativeAtom_sequence_positive i (k + 1) (by omega)]
  have hi : ((i + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Exact signed pairing, including the first site and the complete adjoint row. -/
theorem fixedMismatch_eq_adjoint_pairing (n i : ℕ) :
    fixedMismatch n i = inner ℝ (hilbertOne - projection n) (derivativeAdjointRow i) := by
  rw [fixedMismatch, derivativeResidual, real_inner_comm]
  exact (ContinuousLinearMap.adjoint_inner_right hilbertDifference
    (hilbertOne - projection n) (derivativeAtom i)).symm

theorem fixedMismatch_limit_eq_adjoint_pairing (i : ℕ) :
    inner ℝ (derivativeAtom i) (hilbertDifference limitResidual) =
      inner ℝ limitResidual (derivativeAdjointRow i) := by
  rw [real_inner_comm]
  exact (ContinuousLinearMap.adjoint_inner_right hilbertDifference
    limitResidual (derivativeAtom i)).symm

/-- At conductor two, the periodic part is multiplied by (k+1)/(k+2). -/
theorem derivativeAdjointRow_zero_sequence (k : ℕ) (hk : 0 < k) :
    hilbertSequence (derivativeAdjointRow 0) k =
      ((k : ℝ) + 1) / ((k : ℝ) + 2) *
        (4 * residueFraction 2 k - 1) := by
  rw [derivativeAdjointRow_sequence 0 k hk]
  norm_num only [Nat.zero_add, Nat.cast_ofNat]
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  by_cases he : 2 ∣ k
  · have hm : k % 2 = 0 := Nat.mod_eq_zero_of_dvd he
    have hne : ¬ 2 ∣ k + 1 := by
      intro h
      have h' := Nat.mod_eq_zero_of_dvd h
      omega
    simp only [divisorIndicator, if_pos he, if_neg hne, residueFraction, hm,
      Nat.cast_zero, zero_div, mul_zero, zero_sub, add_zero]
    field_simp
    ring
  · have hm : k % 2 = 1 := by
      have hlt := Nat.mod_lt k (by omega : 0 < 2)
      have hn : k % 2 ≠ 0 := fun h => he (Nat.dvd_of_mod_eq_zero h)
      omega
    have hyes : 2 ∣ k + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    simp only [divisorIndicator, if_neg he, if_pos hyes, residueFraction, hm,
      Nat.cast_one, sub_zero, mul_one]
    field_simp
    ring

/-- The slowly weighted signed remainder is an actual Hilbert vector. -/
def firstRowRemainder : ThresholdHilbert :=
  (4 : ℝ) • residueAtom 0 - hilbertOne - derivativeAdjointRow 0

theorem firstRowRemainder_sequence (k : ℕ) (hk : 0 < k) :
    hilbertSequence firstRowRemainder k =
      (4 * residueFraction 2 k - 1) / ((k : ℝ) + 2) := by
  rw [firstRowRemainder, hilbertSequence_sub, hilbertSequence_sub,
    hilbertSequence_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [residueAtom, normalizedResidueHilbert_sequence,
    hilbertOne_sequence, derivativeAdjointRow_zero_sequence k hk]
  simp only [zeroAnchor,
    if_neg (Nat.ne_of_gt hk), Nat.zero_add]
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The legal normal equation removes its legal term, but this complete
signed remainder survives. In particular no zero limit is inferred. -/
theorem fixedMismatch_first_limit_exact :
    inner ℝ (derivativeAtom 0) (hilbertDifference limitResidual) =
      -limitEnergy - inner ℝ limitResidual firstRowRemainder := by
  have hmem : residueAtom 0 ∈ closedSpace :=
    (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
      (Submodule.subset_span ⟨0, rfl⟩)
  have ho : inner ℝ limitResidual (residueAtom 0) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hmem
  rw [fixedMismatch_limit_eq_adjoint_pairing]
  have he : inner ℝ limitResidual firstRowRemainder =
      -limitEnergy - inner ℝ limitResidual (derivativeAdjointRow 0) := by
    rw [firstRowRemainder, inner_sub_right, inner_sub_right, real_inner_smul_right,
      ho, limitResidual_inner_one]
    ring
  linarith

end CoefficientStabilization.DerivativeCompatibility
end RiemannResearch.RH.Pareto
