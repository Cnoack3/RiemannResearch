/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTMinimumEnergy
import RiemannResearch.RH.QResidueEnergyCertificates
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Explicit correction blocks for the actual primorial CRT family

Source: user-provided Minimum_Energy_Exact_Head_Research_Agenda_2026-10-28.md,
priorities 1 and 2. Sparse or dense real coefficients give actual legal,
head-preserving corrections. The signed gain criterion is a finite certificate
interface; a stage-independent arithmetic provider remains open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTCorrectionCertificates
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace
open QCRTCoprimeApproximation QSquarefreeAffineHead ZetaTwoProbability
open QCRTMinimumEnergy QResidueEnergyCertificates

/-- Concrete CRT specialization: actual zero-head corrections preserve legality and head. -/
theorem correctedSeed_legal_exact_head (j : ℕ) (u : QHilbert)
    (hu : u ∈ dictionary (conductors (primorial (j + 2))) ⊓ headNull (j + 1)) :
    approximant j - u ∈ qSquarefreeCRTSpan ∧
      ∀ n, 0 < n → n ≤ j + 1 → qSequence (approximant j - u) n = 1 := by
  obtain ⟨hm, hh⟩ := correction_same_head _ _ _ _ (seed_mem_dictionary j) hu
  constructor
  · apply divisorStage_le_squarefreeSpan _ (primorial_pos _) (squarefree_primorial _)
    rw [divisorStage_eq_dictionary _ (primorial_pos _)]
    exact hm
  · intro n hn hnj
    exact (hh n hn hnj).trans (approximant_exact_head j n hn hnj)

/-- Stagewise signed certificate for the actual minimum-energy primorial family. -/
theorem minimumEnergyApproximant_le_of_correction_certificate
    (j : ℕ) (u : QHilbert)
    (hu : u ∈ dictionary (conductors (primorial (j + 2))) ⊓ headNull (j + 1))
    (C : ℝ)
    (hgain : ‖approximant j‖ ^ 2 - C ≤
      2 * inner ℝ (approximant j) u - ‖u‖ ^ 2) :
    ‖minimumEnergyApproximant j‖ ^ 2 ≤ C :=
  exactHeadAdjustment_le_of_correction_certificate _ _ _ _ hu C hgain

/-- The actual CRT minimum is no larger than the optimum along any nonzero block. -/
theorem minimumEnergyApproximant_le_one_direction (j : ℕ) (v : QHilbert)
    (hv : v ∈ dictionary (conductors (primorial (j + 2))) ⊓ headNull (j + 1))
    (hv0 : v ≠ 0) :
    ‖minimumEnergyApproximant j‖ ^ 2 ≤ ‖approximant j‖ ^ 2 -
      (inner ℝ (approximant j) v) ^ 2 / ‖v‖ ^ 2 :=
  exactHeadAdjustment_le_one_direction _ _ _ _ hv hv0

open RiemannResearch.Analysis.FiniteHilbertGram

/-- Any real coefficients on the checked compensated basis define an actual correction. -/
def correctionBlock (j : ℕ)
    (a : freeConductors (conductors (primorial (j + 2)))
      (j + 1) (primorial (j + 2)) → ℝ) : QHilbert :=
  Fintype.linearCombination ℝ
    (fun d : freeConductors (conductors (primorial (j + 2)))
      (j + 1) (primorial (j + 2)) => compensatedResidue (d : ℕ) (primorial (j + 2))) a

theorem correctionBlock_mem (j : ℕ)
    (a : freeConductors (conductors (primorial (j + 2)))
      (j + 1) (primorial (j + 2)) → ℝ) :
    correctionBlock j a ∈
      dictionary (conductors (primorial (j + 2))) ⊓ headNull (j + 1) := by
  classical
  have hL : j + 1 < primorial (j + 2) :=
    lt_of_lt_of_le (by omega : j + 1 < j + 2) le_primorial_self
  have hr : primorial (j + 2) ∈ conductors (primorial (j + 2)) :=
    Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨dvd_refl _, primorial_ne_zero _⟩, by omega⟩
  have hm : correctionBlock j a ∈ zeroHeadSpan
      (conductors (primorial (j + 2))) (j + 1) (primorial (j + 2)) := by
    rw [correctionBlock, Fintype.linearCombination_apply]
    exact (zeroHeadSpan _ _ _).sum_mem fun d _ =>
      (zeroHeadSpan _ _ _).smul_mem _ (Submodule.subset_span ⟨d, rfl⟩)
  exact ⟨zeroHeadSpan_le_dictionary _ _ _ hr hm,
    zeroHeadSpan_le_headNull _ _ _ hL hm⟩

/-- The coefficient certificate keeps every signed source and Gram cross term. -/
theorem minimumEnergyApproximant_le_block_certificate (j : ℕ)
    (a : freeConductors (conductors (primorial (j + 2)))
      (j + 1) (primorial (j + 2)) → ℝ) (C : ℝ)
    (hgain : ‖approximant j‖ ^ 2 - C ≤
      2 * (∑ d, a d * inner ℝ
        (compensatedResidue (d : ℕ) (primorial (j + 2))) (approximant j)) -
      ∑ d, a d * gram
        (fun e : freeConductors (conductors (primorial (j + 2)))
          (j + 1) (primorial (j + 2)) => compensatedResidue (e : ℕ) (primorial (j + 2))) a d) :
    ‖minimumEnergyApproximant j‖ ^ 2 ≤ C := by
  apply minimumEnergyApproximant_le_of_correction_certificate j
    (correctionBlock j a) (correctionBlock_mem j a) C
  rw [← real_inner_comm (approximant j) (correctionBlock j a)]
  simpa only [correctionBlock, inner_synthesis_left, gram_quadratic] using hgain

end RiemannResearch.RH.QCRTCorrectionCertificates
