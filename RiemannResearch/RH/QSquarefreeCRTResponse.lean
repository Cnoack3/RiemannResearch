/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalConditioning
import RiemannResearch.RH.QProjectionMoments
import RiemannResearch.RH.QPolylogMovingHeadEnergy
import RiemannResearch.RH.QSquarefreeSignedNormal
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact squarefree projection after CRT conditioning

Source: the user's infinite-CRT response request, 26 October 2026.
The conditioned reciprocal source has a common weighted-energy budget. When
the CRT modulus contains the active conductors, its actual legal projection
equals movingCorrection exactly. The removed remainder and its signed weighted
cross term are retained. Bounding the source does not bound this projection;
the full constant-energy obligation sufficient for RH remains open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeCRTResponse
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QReciprocalConditioning QPolylogTailEnergy QSquarefreeSignedNormal

/-- Common constant for every actual squarefree residual and every CRT modulus.
The output here is the conditioned source, not its legal projected correction. -/
theorem conditionalReciprocal_residual_energy_le
    (L : ℕ) (hL : 0 < L) (N : ℕ) :
    (∑' n, polylogWeightedEnergyTerm 2
      (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N)) n) ≤
      ∑' n : ℕ, 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2) := by
  have hnorm : ‖ZetaTwoOptimizerStage.residual N‖ ^ 2 ≤ 1 := by
    have h := qProjection_error_eq (ZetaTwoOptimizerStage.stage N)
    change ‖ZetaTwoOptimizerStage.residual N‖ ^ 2 =
      1 - ‖(ZetaTwoOptimizerStage.stage N).starProjection qOne‖ ^ 2 at h
    nlinarith [sq_nonneg ‖(ZetaTwoOptimizerStage.stage N).starProjection qOne‖]
  have hmass : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2) :=
    tsum_nonneg (fun n => by positivity)
  exact (conditionalReciprocal_energy_le L hL (ZetaTwoOptimizerStage.residual N)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm hmass)

/-- Every physical head of the conditioned source has that same constant budget. -/
theorem conditionalReciprocal_residual_head_energy_le
    (L : ℕ) (hL : 0 < L) (N H : ℕ) :
    weightedHeadEnergy 2 H
      (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N)) ≤
      ∑' n : ℕ, 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2) := by
  have hh := (conditionalReciprocal_energy_summable L hL
    (ZetaTwoOptimizerStage.residual N)).sum_le_tsum (Finset.range (H + 1))
      (fun n _ => polylogWeightedEnergyTerm_nonneg 2 _ n)
  exact hh.trans (conditionalReciprocal_residual_energy_le L hL N)

/-- The actual finite legal projection may be applied after CRT conditioning.
This is equality of projections, not weighted boundedness of that projection. -/
theorem stage_projection_conditionalReciprocal
    (N L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L)
    (f : QHilbert) :
    (ZetaTwoOptimizerStage.stage N).starProjection (conditionalReciprocal L hL f) =
      (ZetaTwoOptimizerStage.stage N).starProjection (B f) := by
  obtain ⟨c, hc, hcn⟩ := exists_projection_coefficients N (B f)
  have hnormal : Normal N (conditionalReciprocal L hL f) c := by
    intro i
    rw [hcn i]
    by_cases hi : Squarefree (i.val + 2)
    · simp only [ZetaTwoOptimizerStage.squarefreeAtom, if_pos hi]
      exact (conditionalReciprocal_inner_residue L (i.val + 2) hL (hdiv i hi) f).symm
    · simp only [ZetaTwoOptimizerStage.squarefreeAtom, if_neg hi, inner_zero_left]
  exact (synthesis_eq_projection hnormal).symm.trans hc

/-- Exact actual-source CRT reduction, retaining the legal projection. -/
theorem movingCorrection_eq_conditioned_projection
    (N L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    QSquarefreeSmoothedProjection.movingCorrection N =
      (ZetaTwoOptimizerStage.stage N).starProjection
        (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N)) := by
  exact (stage_projection_conditionalReciprocal N L hL hdiv
    (ZetaTwoOptimizerStage.residual N)).symm

/-- The part of the bounded conditional source removed by the legal projection. -/
def conditionedRemainder (N L : ℕ) (hL : 0 < L) : QHilbert :=
  conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N) -
    QSquarefreeSmoothedProjection.movingCorrection N

theorem conditioned_source_split (N L : ℕ) (hL : 0 < L) :
    conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N) =
      QSquarefreeSmoothedProjection.movingCorrection N + conditionedRemainder N L hL := by
  simp [conditionedRemainder]

/-- This is ordinary Q orthogonality, not orthogonality for the head-energy weight. -/
theorem conditionedRemainder_mem_orthogonal (N L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    conditionedRemainder N L hL ∈ (ZetaTwoOptimizerStage.stage N)ᗮ := by
  unfold conditionedRemainder
  rw [movingCorrection_eq_conditioned_projection N L hL hdiv]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- The complete signed finite-head identity retains the new weighted cross term. -/
theorem conditioned_source_weighted_energy_exact (k N L H : ℕ) (hL : 0 < L) :
    weightedHeadEnergy k H
        (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N)) =
      weightedHeadEnergy k H (QSquarefreeSmoothedProjection.movingCorrection N) +
      weightedHeadEnergy k H (conditionedRemainder N L hL) +
      2 * weightedHeadCross k H
        (QSquarefreeSmoothedProjection.movingCorrection N) (conditionedRemainder N L hL) := by
  rw [conditioned_source_split N L hL, weightedHeadEnergy_add_exact]

/-- Arbitrarily chosen actual stages satisfy the infinite-modulus limit
in the complete k=2 energy. No stage-convergence assumption is required. -/
theorem conditionalReciprocal_residual_weighted_error_tendsto_zero
    (S L : ℕ → ℕ) (hLp : ∀ j, 0 < L j) (hL : Tendsto L atTop atTop) :
    Tendsto (fun j => ∑' n : ℕ, polylogWeightedEnergyTerm 2
      (conditionalReciprocal (L j) (hLp j) (ZetaTwoOptimizerStage.residual (S j)) -
        B (ZetaTwoOptimizerStage.residual (S j))) n) atTop (𝓝 0) := by
  apply conditionalReciprocal_weighted_error_tendsto_zero
    (fun j => ZetaTwoOptimizerStage.residual (S j)) 1 (by positivity) _ L hLp hL
  intro j
  have h := qProjection_error_eq (ZetaTwoOptimizerStage.stage (S j))
  change ‖ZetaTwoOptimizerStage.residual (S j)‖ ^ 2 =
    1 - ‖(ZetaTwoOptimizerStage.stage (S j)).starProjection qOne‖ ^ 2 at h
  nlinarith [sq_nonneg ‖(ZetaTwoOptimizerStage.stage (S j)).starProjection qOne‖,
    norm_nonneg (ZetaTwoOptimizerStage.residual (S j))]

end RiemannResearch.RH.QSquarefreeCRTResponse
