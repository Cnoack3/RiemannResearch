/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalTargetLift
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The unit-ball version of the finite bounded-lift existence problem

Source: the user's 14 November 2026 bounded-lift and weak-star compactness
request. BoundedInjectiveLift supplies the compactness argument. Orthogonal
projection supplies the explicit finite inverse-Gram sequence and radius 1.

If any finite legal D-lift with a uniform finite norm bound exists, then the
fixed inverse-Gram candidates converge strongly to 1 and all have norm at
most 1. This is an existence equivalence, not a claim that termwise
normalization of an arbitrary sequence preserves its target. The missing
arithmetic premise is still qOne in the full legal closure, or equivalently
convergence of the D-images of these fixed unit-ball candidates to D1.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QFullResidueProjection
open ZetaTwoHilbert QReciprocalMetric QReciprocalTargetLift

/-- The actual inverse-Gram candidate already lies in the closed unit ball. -/
theorem candidate_norm_le_one (N : ℕ) : ‖candidate N‖ ≤ 1 := by
  rw [candidate_eq_projection]
  simpa only [qOne_norm] using (stage N).norm_starProjection_apply_le qOne

/-- Existence with any finite radius is equivalent to existence of finite
legal unit-ball approximants that converge strongly before applying D. -/
theorem bounded_finite_D_lift_iff_unit_strong_lift :
    (∃ C : ℝ, ∃ F : ℕ → QHilbert,
      (∀ j, F j ∈ legalSpan) ∧ (∀ j, ‖F j‖ ≤ C) ∧
      Tendsto (fun j => D (F j)) atTop (𝓝 (D qOne))) ↔
    (∃ F : ℕ → QHilbert,
      (∀ j, F j ∈ legalSpan) ∧ (∀ j, ‖F j‖ ≤ 1) ∧
      Tendsto F atTop (𝓝 qOne)) := by
  constructor
  · rintro ⟨C, F, hm, hb, ht⟩
    have hx := (mem_of_bounded_D_tendsto closure C F qOne
      (fun j => legalSpan.le_topologicalClosure (hm j)) hb ht).1
    exact ⟨candidate, candidate_mem_legalSpan, candidate_norm_le_one,
      candidate_tendsto_qOne hx⟩
  · rintro ⟨F, hm, hb, ht⟩
    exact ⟨1, F, hm, hb, (D.continuous.tendsto qOne).comp ht⟩

/-- A single explicit, uniformly bounded sequence suffices to test the
existence problem; its smoothed convergence is the unresolved arithmetic input. -/
theorem candidate_D_tendsto_iff_mem :
    Tendsto (fun N => D (candidate N)) atTop (𝓝 (D qOne)) ↔
      qOne ∈ closure := by
  constructor
  · intro ht
    exact (mem_of_bounded_D_tendsto closure 1 candidate qOne
      (fun N => legalSpan.le_topologicalClosure (candidate_mem_legalSpan N))
      candidate_norm_le_one ht).1
  · intro hx
    exact (D.continuous.tendsto qOne).comp (candidate_tendsto_qOne hx)

end RiemannResearch.RH.QFullResidueProjection
