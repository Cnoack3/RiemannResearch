/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.BoundedInjectiveLift
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QShiftedReciprocal

/-!
# Target-specific bounded reciprocal lifts

Source: Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf, Theorem 8.1.
The operator called R in that report is QShiftedReciprocal.B here.
The full-norm bound remains an open arithmetic provider in the RH consumer.

The arithmetic norm bound is not supplied by compactness.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QBoundedReciprocalLift
open ZetaTwoHilbert QShiftedReciprocal QFullResidueProjection

theorem reciprocal_injective : Function.Injective B := by
  intro f g h
  apply sub_eq_zero.mp
  apply B_faithful (f - g)
  have hz : B (f - g) = 0 := by rw [map_sub, h, sub_self]
  rw [hz, inner_zero_right]

/-- The compactness-and-injectivity theorem applies to any complete separable
legal subspace, including the full and squarefree closures. -/
theorem mem_of_bounded_reciprocal_tendsto (S : Submodule ℝ QHilbert)
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (C : ℝ) (F : ℕ → QHilbert) (x : QHilbert)
    (hmem : ∀ n, F n ∈ S) (hbound : ∀ n, ‖F n‖ ≤ C)
    (hlim : Tendsto (fun n => B (F n)) atTop (𝓝 (B x))) :
    x ∈ S ∧ ‖x‖ ≤ C :=
  S.mem_of_bounded_injective_image_tendsto B reciprocal_injective
    C F x hmem hbound hlim

/-- Conditional RH reduction: image convergence is not enough without the bound. -/
theorem riemannHypothesis_of_bounded_reciprocal_target
    (C : ℝ) (F : ℕ → QHilbert)
    (hmem : ∀ n, F n ∈ closure) (hbound : ∀ n, ‖F n‖ ≤ C)
    (hlim : Tendsto (fun n => B (F n)) atTop (𝓝 (B qOne))) :
    RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (mem_of_bounded_reciprocal_tendsto closure C F qOne hmem hbound hlim).1

end RiemannResearch.RH.QBoundedReciprocalLift
