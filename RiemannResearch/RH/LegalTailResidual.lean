/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LegalTailMeanCapacityDilation
import RiemannResearch.RH.ThresholdHilbertAdjoint

/-!
# Physical residual of a legal tail projection

Source: Christian Noack, legal tail-capacity weak-star handoff, November 2026.
The index `K` counts the deleted positive sites. Its physical scale is `K+1`.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open FiniteHeadRepair RiemannResearch.Analysis.SingleObservationProjection

def legalTailResidual (K : ℕ) : ThresholdHilbert :=
  paretoTail K - legalTailMeanVector K

def tailCapacityDeficit (K : ℕ) : ℝ := 1 - normalizedLegalTailMeanCapacity K

theorem tailCapacityDeficit_bounds (K : ℕ) :
    0 ≤ tailCapacityDeficit K ∧ tailCapacityDeficit K ≤ 1 := by
  have h := (legalTailMeanCapacity_normalized_bounds K).2
  have hp := legalTailMeanCapacity_pos K
  unfold tailCapacityDeficit normalizedLegalTailMeanCapacity
  exact ⟨sub_nonneg.mpr h, sub_le_self _ (mul_nonneg (by positivity) hp.le)⟩

theorem legalTailResidual_scaled_energy (K : ℕ) :
    ((K : ℝ) + 1) * ‖legalTailResidual K‖ ^ 2 = tailCapacityDeficit K := by
  have he := projection_defect_energy (legalHeadKernel K) (paretoTail K)
  change ‖legalTailResidual K‖ ^ 2 = ‖paretoTail K‖ ^ 2 - legalTailMeanCapacity K at he
  rw [he, paretoTail_norm_sq, tailCapacityDeficit, normalizedLegalTailMeanCapacity, mul_sub]
  field_simp

theorem legalTailResidual_orthogonal {K : ℕ} {v : ThresholdHilbert}
    (hv : v ∈ legalHeadKernel K) : inner ℝ (legalTailResidual K) v = 0 :=
  Submodule.starProjection_inner_eq_zero _ _ hv

theorem legalTailResidual_inner_tail (K : ℕ) :
    inner ℝ (legalTailResidual K) (paretoTail K) = ‖legalTailResidual K‖ ^ 2 := by
  have hr : paretoTail K = legalTailResidual K + legalTailMeanVector K := by
    simp [legalTailResidual]
  conv_lhs => arg 3; rw [hr]
  rw [inner_add_right, legalTailResidual_orthogonal (legalTailMeanVector_mem K),
    add_zero, real_inner_self_eq_norm_sq]

theorem legalHeadKernel_sequence_zero {K : ℕ} {v : ThresholdHilbert}
    (hv : v ∈ (headMap K).ker) {k : ℕ} (hk : k ≤ K) : hilbertSequence v k = 0 := by
  cases k with
  | zero => rfl
  | succ j =>
    simpa only [headMap_apply, Pi.zero_apply] using
      congrFun (show headMap K v = 0 from hv) (⟨j, by omega⟩ : Fin K)

theorem legalTailResidual_sequence_head {K j : ℕ} (hj : j ≤ K) :
    hilbertSequence (legalTailResidual K) j = 0 := by
  cases j with
  | zero => rfl
  | succ i =>
    rw [legalTailResidual, hilbertSequence_sub, Pi.sub_apply,
      legalHeadKernel_sequence_zero (legalTailMeanVector_mem K).2 hj, sub_zero,
      ← hilbertGibbsPhysical_eq, paretoTail_physical, if_pos (by omega)]

theorem paretoTail_eq_scaled_dilation (K : ℕ) :
    paretoTail K = hilbertTail (K+1) (Nat.succ_pos _) := by
  apply hilbertSequence_injective
  funext j
  rw [hilbertTail_sequence]
  cases j with
  | zero => simp
  | succ j =>
    rw [← hilbertGibbsPhysical_eq, paretoTail_physical]
    by_cases hj : j < K
    · simp [hj, show ¬ K + 1 ≤ j + 1 by omega, show ¬ K ≤ j by omega]
    · simp [hj, show K + 1 ≤ j + 1 by omega, show K ≤ j by omega]

end RiemannResearch.RH.Pareto.PrimePowerSchur
