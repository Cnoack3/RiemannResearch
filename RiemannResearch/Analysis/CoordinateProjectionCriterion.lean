/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Restricted projection criteria from separating continuous coordinates

Source: user-requested restriction of the Pareto coefficient theory to
squarefree atoms, 17 October 2026. The proof combines separation by continuous
coordinates with the existing exhaustive-projection theorem. This is a
functional-analytic criterion, with no arithmetic density hypothesis.

Coordinates omitted by a dictionary vanish on its entire closed span.
If the target also vanishes at omitted coordinates, matching the remaining
coordinates of the limiting projection is equivalent to target membership.
The theorem does not assert totality of the restricted dictionary.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.CoordinateProjectionCriterion
open ExhaustiveWalk

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Vanishing on every atom propagates through the complete norm closure. -/
theorem coordinate_zero_on_closure (v : ℕ → H) (L : H →L[ℝ] ℝ)
    (hzero : ∀ j, L (v j) = 0) {x : H}
    (hx : x ∈ ExhaustiveWalk.dictionaryClosure v) : L x = 0 := by
  have hspan : ∀ y ∈ Submodule.span ℝ (Set.range v), L y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact hzero j
    | zero => exact map_zero L
    | add a b ha hb iha ihb => simp only [map_add, iha, ihb, add_zero]
    | smul c a ha iha => simp only [map_smul, iha, smul_zero]
  exact (closure_minimal hspan
    (isClosed_eq L.continuous continuous_const)) hx

variable [CompleteSpace H]

/-- Only the retained coordinates need matching when the omitted target
coordinates are already zero. Separation is on the ambient Hilbert space. -/
theorem target_mem_iff_limiting_coordinates
    (v : ℕ → H) (L : ℕ → H →L[ℝ] ℝ) (S : Set ℕ)
    (hskip : ∀ i, i ∉ S → ∀ j, L i (v j) = 0)
    (hseparate : ∀ f : H, (∀ i, L i f = 0) → f = 0)
    (x : H) (hxskip : ∀ i, i ∉ S → L i x = 0) :
    x ∈ ExhaustiveWalk.dictionaryClosure v ↔
      ∀ i ∈ S, L i ((ExhaustiveWalk.dictionaryClosure v).starProjection x) = L i x := by
  classical
  constructor
  · intro hx i hi
    rw [Submodule.starProjection_eq_self_iff.mpr hx]
  · intro hmatch
    have hz : x - (ExhaustiveWalk.dictionaryClosure v).starProjection x = 0 := by
      apply hseparate
      intro i
      rw [map_sub]
      by_cases hi : i ∈ S
      · exact sub_eq_zero.mpr (hmatch i hi).symm
      · have hp : L i ((ExhaustiveWalk.dictionaryClosure v).starProjection x) = 0 :=
          coordinate_zero_on_closure v (L i) (hskip i hi)
            ((ExhaustiveWalk.dictionaryClosure v).starProjection_apply_mem x)
        rw [hxskip i hi, hp, sub_self]
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm

/-- The actual finite orthogonal-projection coefficients converge to the
target coordinates exactly when the target belongs to the restricted closure.
Unconditional stabilization follows from `walkProjection_map_tendsto`;
identification of the limits is the substantive condition here. -/
theorem target_mem_iff_coordinate_limits
    (v : ℕ → H) (L : ℕ → H →L[ℝ] ℝ) (S : Set ℕ)
    (hskip : ∀ i, i ∉ S → ∀ j, L i (v j) = 0)
    (hseparate : ∀ f : H, (∀ i, L i f = 0) → f = 0)
    (x : H) (hxskip : ∀ i, i ∉ S → L i x = 0) :
    x ∈ ExhaustiveWalk.dictionaryClosure v ↔
      ∀ i ∈ S, Tendsto
        (fun n => L i ((walkSpan v id n).starProjection x))
        atTop (𝓝 (L i x)) := by
  rw [target_mem_iff_limiting_coordinates v L S hskip hseparate x hxskip]
  constructor
  · intro h i hi
    simpa only [h i hi] using
      walkProjection_map_tendsto v id Function.surjective_id x (L i)
  · intro h i hi
    exact tendsto_nhds_unique
      (walkProjection_map_tendsto v id Function.surjective_id x (L i)) (h i hi)

end RiemannResearch.Analysis.CoordinateProjectionCriterion
