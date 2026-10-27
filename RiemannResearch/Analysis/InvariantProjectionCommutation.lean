/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Self-adjoint operators commute with projections onto invariant subspaces

The exact identity is used for arithmetic prime-resampling projections.
It avoids exchanging two infinite geometric sums. The proof applies Mathlib's
`Submodule.eq_starProjection_of_mem_of_inner_eq_zero` characterization.
-/

noncomputable section
namespace RiemannResearch.Analysis.InvariantProjectionCommutation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem map_starProjection_eq
    (U : Submodule ℝ H) [U.HasOrthogonalProjection]
    (T : H →L[ℝ] H)
    (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hU : ∀ x : H, x ∈ U → T x ∈ U) (x : H) :
    T (U.starProjection x) = U.starProjection (T x) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hU (U.starProjection x) (U.starProjection_apply_mem x))
  intro w hw
  rw [← map_sub, hT]
  exact U.starProjection_inner_eq_zero x (T w) (hU w hw)

end RiemannResearch.Analysis.InvariantProjectionCommutation
