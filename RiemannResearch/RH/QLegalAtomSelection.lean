/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RandomSubspaceProjection
import RiemannResearch.Analysis.FiniteAtomSelection
import RiemannResearch.RH.QLegalResidueDPP
import RiemannResearch.Probability.FiniteDeterminantalLaw

/-!
# Random selections from actual legal residue dictionaries

Source: user-provided nested-projection and sampling question, 14 October 2026.
The random indices here are legal atom/conductor indices. They are not the
divisor-wavelet sites of QLegalResidueDPP.fullLaw or squarefreeLaw.
Every sampling identity is exact. Neither legal closure nor RH is assumed;
the mean-square zero limit remains a hypothesis in the RH consumers.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QLegalAtomSelection
open ZetaTwoHilbert QDivisorProjectionDPP QLegalResidueDPP
open RiemannResearch.Analysis
open RandomSubspaceProjection FiniteAtomSelection

def fullSelected (n : ℕ) (J : Finset (Fin n)) : Submodule ℝ QHilbert :=
  selectedSpan (fun i : Fin n => qResidue ((i : ℕ) + 2)) J

instance fullSelected_finiteDimensional (n : ℕ) (J : Finset (Fin n)) :
    FiniteDimensional ℝ (fullSelected n J) := by
  unfold fullSelected
  infer_instance

theorem fullSelected_le (n : ℕ) (J : Finset (Fin n)) :
    fullSelected n J ≤ QFullResidueProjection.stage n := by
  apply selectedSpan_le
  intro i _
  change qResidue ((i : ℕ) + 2) ∈ Submodule.span ℝ
    (Set.range (fun i : Fin n => qResidue (id (i : ℕ) + 2)))
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Only actual squarefree conductors occur in this sampling type. -/
abbrev SquarefreeIndex (n : ℕ) := {i : Fin n // Squarefree ((i : ℕ) + 2)}

def squarefreeSelected (n : ℕ) (J : Finset (SquarefreeIndex n)) : Submodule ℝ QHilbert :=
  selectedSpan (fun i : SquarefreeIndex n => qResidue ((i.1 : ℕ) + 2)) J

instance squarefreeSelected_finiteDimensional (n : ℕ) (J : Finset (SquarefreeIndex n)) :
    FiniteDimensional ℝ (squarefreeSelected n J) := by
  unfold squarefreeSelected
  infer_instance

theorem squarefreeSelected_le (n : ℕ) (J : Finset (SquarefreeIndex n)) :
    squarefreeSelected n J ≤ ZetaTwoOptimizerStage.stage n := by
  apply selectedSpan_le
  intro i _
  change qResidue ((i.1 : ℕ) + 2) ∈ Submodule.span ℝ
    (Set.range (fun i : Fin n => ZetaTwoOptimizerStage.squarefreeAtom (id (i : ℕ))))
  have h : ZetaTwoOptimizerStage.squarefreeAtom (i.1 : ℕ) ∈
      Submodule.span ℝ
        (Set.range (fun i : Fin n => ZetaTwoOptimizerStage.squarefreeAtom (id (i : ℕ)))) :=
    Submodule.subset_span ⟨i.1, rfl⟩
  simpa only [ZetaTwoOptimizerStage.squarefreeAtom, if_pos i.2] using h

theorem full_selection_error (n : ℕ) (J : Finset (Fin n)) :
    ‖qOne - (fullSelected n J).starProjection qOne‖ ^ 2 =
      1 - fullOccupation n +
        ‖QFullResidueProjection.candidate n - (fullSelected n J).starProjection qOne‖ ^ 2 := by
  rw [full_occupation_energy, QFullResidueProjection.candidate_eq_projection,
    sub_sub_cancel]
  exact NestedProjectionEnergy.residual_energy_eq_add_gap (fullSelected_le n J) qOne

theorem squarefree_selection_error (n : ℕ) (J : Finset (SquarefreeIndex n)) :
    ‖qOne - (squarefreeSelected n J).starProjection qOne‖ ^ 2 =
      1 - squarefreeOccupation n +
        ‖(ZetaTwoOptimizerStage.stage n).starProjection qOne -
          (squarefreeSelected n J).starProjection qOne‖ ^ 2 := by
  rw [squarefree_occupation_energy, sub_sub_cancel]
  exact NestedProjectionEnergy.residual_energy_eq_add_gap
    (squarefreeSelected_le n J) qOne

theorem full_expected_error (n : ℕ) (p : Finset (Fin n) → ℝ)
    (hsum : ∑ J, p J = 1) :
    expectedError (fullSelected n) p qOne =
      1 - fullOccupation n +
        expectedGap (QFullResidueProjection.stage n) (fullSelected n) p qOne := by
  rw [full_occupation_energy, QFullResidueProjection.candidate_eq_projection,
    sub_sub_cancel]
  exact expected_error_eq _ _ p hsum (fullSelected_le n) qOne

theorem squarefree_expected_error (n : ℕ) (p : Finset (SquarefreeIndex n) → ℝ)
    (hsum : ∑ J, p J = 1) :
    expectedError (squarefreeSelected n) p qOne =
      1 - squarefreeOccupation n +
        expectedGap (ZetaTwoOptimizerStage.stage n) (squarefreeSelected n) p qOne := by
  rw [squarefree_occupation_energy, sub_sub_cancel]
  exact expected_error_eq _ _ p hsum (squarefreeSelected_le n) qOne

theorem full_expected_error_eq_iff (n : ℕ) (p : Finset (Fin n) → ℝ)
    (hp : ∀ J, 0 ≤ p J) (hsum : ∑ J, p J = 1) :
    expectedError (fullSelected n) p qOne = 1 - fullOccupation n ↔
      ∀ J, 0 < p J → QFullResidueProjection.candidate n ∈ fullSelected n J := by
  rw [full_occupation_energy, QFullResidueProjection.candidate_eq_projection,
    sub_sub_cancel]
  exact expected_error_eq_iff _ _ p hp hsum (fullSelected_le n) qOne

theorem squarefree_expected_error_eq_iff (n : ℕ) (p : Finset (SquarefreeIndex n) → ℝ)
    (hp : ∀ J, 0 ≤ p J) (hsum : ∑ J, p J = 1) :
    expectedError (squarefreeSelected n) p qOne = 1 - squarefreeOccupation n ↔
      ∀ J, 0 < p J → (ZetaTwoOptimizerStage.stage n).starProjection qOne ∈
        squarefreeSelected n J := by
  rw [squarefree_occupation_energy, sub_sub_cancel]
  exact expected_error_eq_iff _ _ p hp hsum (squarefreeSelected_le n) qOne

theorem full_sampling_tendsto_zero_iff
    (p : (n : ℕ) → Finset (Fin n) → ℝ) (hp : ∀ n J, 0 ≤ p n J)
    (hsum : ∀ n, ∑ J, p n J = 1) :
    Tendsto (fun n => expectedError (fullSelected n) (p n) qOne) atTop (𝓝 0) ↔
      Tendsto fullOccupation atTop (𝓝 1) ∧
      Tendsto (fun n => expectedGap (QFullResidueProjection.stage n)
        (fullSelected n) (p n) qOne) atTop (𝓝 0) := by
  have hi :
      Tendsto (fun n => ‖qOne - (QFullResidueProjection.stage n).starProjection qOne‖ ^ 2)
        atTop (𝓝 0) ↔ Tendsto fullOccupation atTop (𝓝 1) := by
    constructor
    · intro h
      have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa only [← QFullResidueProjection.candidate_eq_projection,
        ← full_occupation_energy, sub_zero] using hc.sub h
    · intro h
      have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa only [full_occupation_energy, QFullResidueProjection.candidate_eq_projection,
        sub_sub_cancel, sub_self] using hc.sub h
  exact (expected_error_tendsto_zero_iff QFullResidueProjection.stage
    fullSelected p hp hsum fullSelected_le qOne).trans (and_congr hi Iff.rfl)

theorem squarefree_sampling_tendsto_zero_iff
    (p : (n : ℕ) → Finset (SquarefreeIndex n) → ℝ) (hp : ∀ n J, 0 ≤ p n J)
    (hsum : ∀ n, ∑ J, p n J = 1) :
    Tendsto (fun n => expectedError (squarefreeSelected n) (p n) qOne) atTop (𝓝 0) ↔
      Tendsto squarefreeOccupation atTop (𝓝 1) ∧
      Tendsto (fun n => expectedGap (ZetaTwoOptimizerStage.stage n)
        (squarefreeSelected n) (p n) qOne) atTop (𝓝 0) := by
  have hi :
      Tendsto (fun n => ‖qOne - (ZetaTwoOptimizerStage.stage n).starProjection qOne‖ ^ 2)
        atTop (𝓝 0) ↔ Tendsto squarefreeOccupation atTop (𝓝 1) := by
    constructor
    · intro h
      have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have he : squarefreeOccupation =
          (fun n => 1 - ‖qOne - (ZetaTwoOptimizerStage.stage n).starProjection qOne‖ ^ 2) := by
        funext n
        exact squarefree_occupation_energy n
      rw [he]
      simpa only [sub_zero] using hc.sub h
    · intro h
      have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa only [squarefree_occupation_energy, ZetaTwoOptimizerStage.error,
        ZetaTwoOptimizerStage.residual, ZetaTwoOptimizerStage.optimizer,
        sub_sub_cancel, sub_self]
        using hc.sub h
  exact (expected_error_tendsto_zero_iff ZetaTwoOptimizerStage.stage
    squarefreeSelected p hp hsum squarefreeSelected_le qOne).trans (and_congr hi Iff.rfl)

/-- Conditional research reduction: no provider of the zero limit is asserted. -/
theorem riemannHypothesis_of_full_expected_error_tendsto_zero
    (p : (n : ℕ) → Finset (Fin n) → ℝ) (hp : ∀ n J, 0 ≤ p n J)
    (hsum : ∀ n, ∑ J, p n J = 1)
    (h : Tendsto (fun n => expectedError (fullSelected n) (p n) qOne) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_fullOccupation_tendsto_one
    ((full_sampling_tendsto_zero_iff p hp hsum).mp h).1

/-- Conditional research reduction for selections of actual squarefree conductors. -/
theorem riemannHypothesis_of_squarefree_expected_error_tendsto_zero
    (p : (n : ℕ) → Finset (SquarefreeIndex n) → ℝ) (hp : ∀ n J, 0 ≤ p n J)
    (hsum : ∀ n, ∑ J, p n J = 1)
    (h : Tendsto (fun n => expectedError (squarefreeSelected n) (p n) qOne)
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_squarefreeOccupation_tendsto_one
    ((squarefree_sampling_tendsto_zero_iff p hp hsum).mp h).1


/-- Explicit two-stage connection: first select conductors, then sample the
wavelet law of the selected span. A mixture is not asserted to be a DPP. -/
theorem full_mixed_wavelet_vacancy (n : ℕ) (p : Finset (Fin n) → ℝ)
    (hsum : ∑ J, p J = 1) :
    (∑ J, p J * (modeLaw (fullSelected n J)).real {x | x 1 = false}) =
      1 - fullOccupation n +
        expectedGap (QFullResidueProjection.stage n) (fullSelected n) p qOne := by
  simpa only [expectedError, constant_vacancy] using full_expected_error n p hsum

theorem squarefree_mixed_wavelet_vacancy (n : ℕ)
    (p : Finset (SquarefreeIndex n) → ℝ) (hsum : ∑ J, p J = 1) :
    (∑ J, p J * (modeLaw (squarefreeSelected n J)).real {x | x 1 = false}) =
      1 - squarefreeOccupation n +
        expectedGap (ZetaTwoOptimizerStage.stage n) (squarefreeSelected n) p qOne := by
  simpa only [expectedError, constant_vacancy] using squarefree_expected_error n p hsum

open RiemannResearch.Probability.DPP

/-- The conductor law is the existing finite PMF, with conductor-indexed K. -/
theorem full_conductorDPP_expected_error (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.PosSemidef) (hI : (1 - K).PosSemidef) :
    expectedError (fullSelected n)
      (fun J => ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal) qOne =
      1 - fullOccupation n +
        expectedGap (QFullResidueProjection.stage n) (fullSelected n)
          (fun J => ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal) qOne := by
  apply full_expected_error
  simpa only [finiteLaw_apply_toReal] using sum_exactWeight K

theorem squarefree_conductorDPP_expected_error (n : ℕ)
    (K : Matrix (SquarefreeIndex n) (SquarefreeIndex n) ℝ)
    (hK : K.PosSemidef) (hI : (1 - K).PosSemidef) :
    expectedError (squarefreeSelected n)
      (fun J => ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal) qOne =
      1 - squarefreeOccupation n +
        expectedGap (ZetaTwoOptimizerStage.stage n) (squarefreeSelected n)
          (fun J => ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal) qOne := by
  apply squarefree_expected_error
  simpa only [finiteLaw_apply_toReal] using sum_exactWeight K

end RiemannResearch.RH.QLegalAtomSelection
