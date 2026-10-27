/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLegalMixedConductorWeightedEnergy
import RiemannResearch.RH.QReciprocalWeightedEnergy

/-!
# Actual weighted-L2 projection transfer fails uniformly over legal subspaces

Source: LegalSubspaceProjectionObstruction.md. This deterministic obstruction
has all arithmetic providers discharged. It does not identify the weighted
energy with a prime-resampling Dirichlet form, and it makes no assertion
against the special canonical increasing squarefree stages.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QLegalMixedConductor
open ZetaTwoHilbert QShiftedReciprocal QPolylogTailEnergy ZetaTwoOptimizerStage

def rawSourceWeightedEnergy (d : ℕ) : ℝ :=
  ∑' n : ℕ, polylogWeightedEnergyTerm 2 (B (actualResidual d)) n

theorem rawSourceWeightedEnergy_nonneg (d : ℕ) : 0 ≤ rawSourceWeightedEnergy d :=
  tsum_nonneg (polylogWeightedEnergyTerm_nonneg 2 (B (actualResidual d)))

theorem actualResidual_norm_sq_le_quarter (d : ℕ) : ‖actualResidual d‖ ^ 2 ≤ 1 / 4 := by
  nlinarith [actualResidual_norm_le_half d, norm_nonneg (actualResidual d)]

theorem rawSourceWeightedEnergy_le_1024 (d : ℕ) : rawSourceWeightedEnergy d ≤ 1 / 1024 := by
  have h := reciprocal_weightedEnergy_le (actualResidual d)
  change rawSourceWeightedEnergy d ≤ ‖actualResidual d‖ ^ 2 / 256 at h
  linarith [actualResidual_norm_sq_le_quarter d]

theorem rawSourceWeightedEnergy_le_quarter (d : ℕ) : rawSourceWeightedEnergy d ≤ 1 / 4 := by
  linarith [rawSourceWeightedEnergy_le_1024 d]

/-- Every proposed constant fails on an arbitrarily large actual legal prime
conductor, although the raw weighted forcing and ordinary residual stay bounded. -/
theorem exists_prime_weighted_transfer_failure (C : ℝ) (N : ℕ) :
    ∃ d : ℕ, d.Prime ∧ N ≤ d ∧ 3 < d ∧
      mixedSpace d ≤ Submodule.span ℝ (Set.range squarefreeAtom) ∧
      qResidue 2 ∈ mixedSpace d ∧
      C * (rawSourceWeightedEnergy d + ‖actualResidual d‖ ^ 2) <
        correctionWeightedEnergy d := by
  obtain ⟨d, hp, hdN, hd, hlarge⟩ :=
    exists_prime_actualCorrection_large_weightedEnergy (|C| + 1) N
  refine ⟨d, hp, hdN, hd, mixedSpace_le_legalSpan hp,
    parityAtom_mem_mixedSpace d, ?_⟩
  have hs0 : 0 ≤ rawSourceWeightedEnergy d + ‖actualResidual d‖ ^ 2 :=
    add_nonneg (rawSourceWeightedEnergy_nonneg d) (sq_nonneg _)
  have hs : rawSourceWeightedEnergy d + ‖actualResidual d‖ ^ 2 ≤ 1 := by
    linarith [rawSourceWeightedEnergy_le_quarter d, actualResidual_norm_sq_le_quarter d]
  have hm : C * (rawSourceWeightedEnergy d + ‖actualResidual d‖ ^ 2) ≤ |C| := by
    calc
      _ ≤ |C| * (rawSourceWeightedEnergy d + ‖actualResidual d‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hs0
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg C)
      _ = _ := mul_one _
  linarith [hlarge]

/-- Uniform transfer already fails for deterministic complete weighted L2
energy, without invoking any unformalized probabilistic comparison. -/
theorem no_uniform_actual_weighted_transfer :
    ¬ ∃ C : ℝ, ∀ d : ℕ, d.Prime → 3 < d →
      correctionWeightedEnergy d ≤
        C * (rawSourceWeightedEnergy d + ‖actualResidual d‖ ^ 2) := by
  rintro ⟨C, hC⟩
  obtain ⟨d, hp, _, hd, _, _, hf⟩ := exists_prime_weighted_transfer_failure C 0
  exact (not_lt_of_ge (hC d hp hd)) hf

end RiemannResearch.RH.QLegalMixedConductor
