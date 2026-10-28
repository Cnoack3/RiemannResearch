/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.QSquarefreeAffineHead

/-!
# The actual minimum-energy exact-head CRT family

Source: the user's minimum-energy exact-head research agenda, Section 10,
28 October 2026. Apply the complete-Q orthogonal correction to the checked
primorial coprime-count seed.

Every output is a finite squarefree legal vector. Its expanding head is
exactly one, so it converges pointwise to one. It is the unique energy
minimizer among all vectors in the same divisor stage with that head.
The matrix formula uses the full Q inner product and an actual inverse.
No uniform norm bound or Riemann Hypothesis conclusion is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTMinimumEnergy
open Filter
open scoped Topology
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets
open QResidueHeadSpace QSquarefreeAffineHead
open QCRTCoprimeApproximation
open RiemannResearch.Analysis.FiniteHilbertGram

def minimumEnergyApproximant (j : ℕ) : QHilbert :=
  exactHeadAdjustment (conductors (primorial (j + 2))) (j + 1) (approximant j)

theorem seed_mem_dictionary (j : ℕ) :
    approximant j ∈ dictionary (conductors (primorial (j + 2))) := by
  rw [← divisorStage_eq_dictionary _ (primorial_pos _)]
  exact coprimeApprox_mem_divisorStage _

theorem minimumEnergyApproximant_mem_dictionary (j : ℕ) :
    minimumEnergyApproximant j ∈ dictionary (conductors (primorial (j + 2))) :=
  (exactHeadAdjustment_same_head _ _ _ (seed_mem_dictionary j)).1

theorem minimumEnergyApproximant_legal (j : ℕ) :
    minimumEnergyApproximant j ∈ qSquarefreeCRTSpan := by
  apply divisorStage_le_squarefreeSpan _ (primorial_pos _) (squarefree_primorial _)
  rw [divisorStage_eq_dictionary _ (primorial_pos _)]
  exact minimumEnergyApproximant_mem_dictionary j

theorem minimumEnergyApproximant_exact_head (j n : ℕ)
    (hn : 0 < n) (hnj : n ≤ j + 1) :
    qSequence (minimumEnergyApproximant j) n = 1 := by
  have h := (exactHeadAdjustment_same_head _ _ _ (seed_mem_dictionary j)).2 n hn hnj
  exact h.trans (approximant_exact_head j n hn hnj)

theorem minimumEnergyApproximant_pointwise (n : ℕ) (hn : 0 < n) :
    Tendsto (fun j => qSequence (minimumEnergyApproximant j) n) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with j hj
  exact (minimumEnergyApproximant_exact_head j n hn (by omega)).symm

theorem minimumEnergyApproximant_energy (j : ℕ) :
    ‖minimumEnergyApproximant j‖ ^ 2 = ‖approximant j‖ ^ 2 -
      ‖(dictionary (conductors (primorial (j + 2))) ⊓ headNull (j + 1)).starProjection
        (approximant j)‖ ^ 2 :=
  exactHeadAdjustment_energy _ _ _

theorem minimumEnergyApproximant_completion (j : ℕ) (f : QHilbert)
    (hf : f ∈ divisorStage (primorial (j + 2)))
    (hh : ∀ n, 0 < n → n ≤ j + 1 → qSequence f n = 1) :
    ‖f‖ ^ 2 = ‖minimumEnergyApproximant j‖ ^ 2 +
      ‖f - minimumEnergyApproximant j‖ ^ 2 := by
  rw [divisorStage_eq_dictionary _ (primorial_pos _)] at hf
  apply exactHeadAdjustment_completion _ _ _ _ (seed_mem_dictionary j) hf
  intro n hn hnj
  rw [hh n hn hnj, approximant_exact_head j n hn hnj]

theorem minimumEnergyApproximant_isLeast (j : ℕ) :
    IsLeast {E : ℝ | ∃ f : QHilbert, f ∈ divisorStage (primorial (j + 2)) ∧
      (∀ n, 0 < n → n ≤ j + 1 → qSequence f n = 1) ∧ ‖f‖ ^ 2 = E}
      (‖minimumEnergyApproximant j‖ ^ 2) := by
  constructor
  · refine ⟨minimumEnergyApproximant j, ?_, minimumEnergyApproximant_exact_head j, rfl⟩
    rw [divisorStage_eq_dictionary _ (primorial_pos _)]
    exact minimumEnergyApproximant_mem_dictionary j
  · rintro E ⟨f, hf, hh, rfl⟩
    rw [minimumEnergyApproximant_completion j f hf hh]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem minimumEnergyApproximant_unique (j : ℕ) (f : QHilbert)
    (hf : f ∈ divisorStage (primorial (j + 2)))
    (hh : ∀ n, 0 < n → n ≤ j + 1 → qSequence f n = 1)
    (he : ‖f‖ ^ 2 = ‖minimumEnergyApproximant j‖ ^ 2) :
    f = minimumEnergyApproximant j := by
  have h := minimumEnergyApproximant_completion j f hf hh
  have hz : ‖f - minimumEnergyApproximant j‖ ^ 2 = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem minimumEnergyApproximant_matrix_value (j : ℕ) :
    let L := primorial (j + 2)
    let v := fun d : freeConductors (conductors L) (j + 1) L =>
      compensatedResidue (d : ℕ) L
    ‖minimumEnergyApproximant j‖ ^ 2 = ‖approximant j‖ ^ 2 -
      dotProduct (cross v (approximant j))
        ((gramMatrix v)⁻¹.mulVec (cross v (approximant j))) := by
  have hL : j + 1 < primorial (j + 2) :=
    lt_of_lt_of_le (by omega : j + 1 < j + 2) le_primorial_self
  have hr : primorial (j + 2) ∈ conductors (primorial (j + 2)) :=
    Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨dvd_refl _, primorial_ne_zero _⟩, by omega⟩
  exact exactHeadAdjustment_matrix_value _ (conductor_gt_one _) _ _ (by omega)
    hr hL _

end RiemannResearch.RH.QCRTMinimumEnergy
