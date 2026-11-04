/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Projection commutation from symmetric invariance

Standard Hilbert-space argument. The concrete RH consumer is the real joint
commutant of the shifted reciprocal and the squarefree legal projection.
-/

namespace Submodule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem starProjection_commutes_of_symmetric_preserves
    (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (A : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (A x) y = inner ℝ x (A y))
    (hpres : ∀ x : H, x ∈ W → A x ∈ W) (x : H) :
    W.starProjection (A x) = A (W.starProjection x) := by
  have hperp : A (x-W.starProjection x) ∈ Wᗮ := by
    apply (W.mem_orthogonal _).mpr
    intro y hy
    rw [← hsym]
    exact Submodule.inner_right_of_mem_orthogonal (hpres y hy)
      (Submodule.sub_starProjection_mem_orthogonal (K := W) x)
  have hz := W.starProjection_apply_eq_zero_iff.mpr hperp
  rw [map_sub, map_sub,
    Submodule.starProjection_eq_self_iff.mpr (hpres _ (W.starProjection_apply_mem x))] at hz
  exact sub_eq_zero.mp hz

end Submodule
