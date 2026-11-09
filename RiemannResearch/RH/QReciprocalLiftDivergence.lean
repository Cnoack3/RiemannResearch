/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.InjectiveLiftDivergence
import RiemannResearch.RH.QBoundedReciprocalLift
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace

/-!
# Unconditional dichotomy for full legal reciprocal approximants

Source: user-provided Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf,
Theorem 8.1, and its 8 November compactness continuation.
Any legal sequence whose reciprocal images converge to R1 either has RH
as a consequence of a bounded subsequence, or has source norm tending to
infinity if RH fails. This is an obstruction, not an RH proof.

-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QReciprocalLiftDivergence
open ZetaTwoHilbert QShiftedReciprocal QFullResidueProjection QBoundedReciprocalLift

/-- Target nonmembership forces complete source-norm divergence. -/
theorem norm_tendsto_atTop_of_not_mem_reciprocal_tendsto
    (S : Submodule ℝ QHilbert) [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (F : ℕ → QHilbert) (x : QHilbert) (hx : x ∉ S)
    (hmem : ∀ n, F n ∈ S)
    (hlim : Tendsto (fun n => B (F n)) atTop (𝓝 (B x))) :
    Tendsto (fun n => ‖F n‖) atTop atTop :=
  S.norm_tendsto_atTop_of_not_mem_injective_image_tendsto
    B reciprocal_injective F x hx hmem hlim

/-- If RH fails, every full-legal reciprocal approximation to the constant
has norm tending to infinity, not merely an unbounded subsequence. -/
theorem reciprocal_target_norm_tendsto_atTop_of_not_RH
    (hRH : ¬ RiemannHypothesis) (F : ℕ → QHilbert)
    (hmem : ∀ n, F n ∈ closure)
    (hlim : Tendsto (fun n => B (F n)) atTop (𝓝 (B qOne))) :
    Tendsto (fun n => ‖F n‖) atTop atTop := by
  apply norm_tendsto_atTop_of_not_mem_reciprocal_tendsto closure F qOne ?_ hmem hlim
  intro hx
  exact hRH (riemannHypothesis_of_qOne_mem_full_closure hx)

end RiemannResearch.RH.QReciprocalLiftDivergence
