/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.BoundedInjectiveLift
import Mathlib.Topology.Order.Basic

/-!
# Divergence of every injective approximate lift outside a closed subspace

Source: user-provided Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf,
Theorem 8.1, and its 8 November compactness continuation.
Failure of divergence produces a uniformly bounded cofinal subsequence.
The existing weak compactness and injectivity theorem then places the target
in the source subspace, a contradiction. No compactness of T is assumed.

-/

noncomputable section
open Filter
open scoped Topology

namespace Submodule

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- When an injective image converges to the image of a target outside S,
the norms of every S-valued lift tend to infinity along the whole sequence. -/
theorem norm_tendsto_atTop_of_not_mem_injective_image_tendsto
    (S : Submodule ℝ H) [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T : H →L[ℝ] K) (hT : Function.Injective T)
    (F : ℕ → H) (x : H) (hx : x ∉ S)
    (hmem : ∀ n, F n ∈ S)
    (hlim : Tendsto (fun n => T (F n)) atTop (𝓝 (T x))) :
    Tendsto (fun n => ‖F n‖) atTop atTop := by
  classical
  apply tendsto_atTop.mpr
  intro C
  by_contra h
  have hcofinal : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ‖F n‖ < C := by
    intro N
    by_contra hn
    have he : ∀ n : ℕ, N ≤ n → C ≤ ‖F n‖ := by
      intro n hnN
      by_contra hsmall
      exact hn ⟨n, hnN, lt_of_not_ge hsmall⟩
    exact h (eventually_atTop.mpr ⟨N, he⟩)
  let φ : ℕ → ℕ := fun N => Classical.choose (hcofinal N)
  have hφge (N : ℕ) : N ≤ φ N := (Classical.choose_spec (hcofinal N)).1
  have hφbound (N : ℕ) : ‖F (φ N)‖ ≤ C :=
    (Classical.choose_spec (hcofinal N)).2.le
  have hφ : Tendsto φ atTop atTop := tendsto_atTop_mono hφge tendsto_id
  exact hx (S.mem_of_bounded_subsequence_injective_image_tendsto
    T hT C F x φ hφ hmem hφbound hlim).1

end Submodule
