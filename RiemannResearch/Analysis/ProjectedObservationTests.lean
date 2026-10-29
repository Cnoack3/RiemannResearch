/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.HilbertWeakNorm
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Internal weak tests and projected finite observations

Source: user-requested Ramanujan weak-star closure argument, 28 October 2026.
No norm bound is assumed. The WeakDual topology is Mathlib's topology of
pointwise convergence on all vectors of the predual:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/Spaces/WeakDual.html
This reference supports the topology, not an arithmetic convergence premise.
The internal tests belong to the complete closed subspace; they need not be
finite algebraic combinations of its generating atoms.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.ProjectedObservationTests
open HilbertWeakNorm
variable {E I J : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
variable (L : Submodule ℝ E) [CompleteSpace L]

theorem projected_test_on_mem (y z : E) (hz : z ∈ L) :
    inner ℝ (L.starProjection y) z = inner ℝ y z := by
  have ho : y - L.starProjection y ∈ Lᗮ :=
    Submodule.sub_starProjection_mem_orthogonal y
  have h := (Submodule.mem_orthogonal' L _).mp ho z hz
  rw [inner_sub_left] at h
  exact (sub_eq_zero.mp h).symm

theorem projected_pairing (y x : E) :
    inner ℝ (L.starProjection y) x = inner ℝ y (L.starProjection x) := by
  have ho : x - L.starProjection x ∈ Lᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  have h := (L.mem_orthogonal _).mp ho (L.starProjection y)
    (L.starProjection_apply_mem y)
  rw [inner_sub_right] at h
  exact (sub_eq_zero.mp h).trans
    (projected_test_on_mem L y _ (L.starProjection_apply_mem x))

theorem internal_tests_tendsto_to_projection {l : Filter I}
    (F : I → E) (x : E) (hF : ∀ᶠ i in l, F i ∈ L)
    (ht : ∀ v : E, v ∈ L →
      Tendsto (fun i => inner ℝ v (F i)) l (𝓝 (inner ℝ v x))) :
    InnerWeakTendsto F l (L.starProjection x) := by
  intro y
  have h := ht (L.starProjection y) (L.starProjection_apply_mem y)
  rw [projected_pairing L y x] at h
  apply h.congr'
  filter_upwards [hF] with i hi
  exact projected_test_on_mem L y (F i) hi

theorem projected_observation_exact_defect (e F x : E)
    (hF : F ∈ L) (hh : inner ℝ e F = inner ℝ e x) :
    inner ℝ (L.starProjection e) (F - x) =
      inner ℝ e (x - L.starProjection x) := by
  simp only [inner_sub_right]
  rw [projected_test_on_mem L e F hF, projected_pairing L e x, hh]

theorem projection_eq_of_projected_exact_tests {l : Filter I} [NeBot l]
    (F : I → E) (x : E) (e : J → E)
    (hsep : ∀ z : E, (∀ j, inner ℝ (e j) z = 0) → z = 0)
    (hF : ∀ᶠ i in l, F i ∈ L)
    (hhead : ∀ j, ∀ᶠ i in l, inner ℝ (e j) (F i) = inner ℝ (e j) x)
    (hint : ∀ j, Tendsto (fun i => inner ℝ (L.starProjection (e j)) (F i - x))
      l (𝓝 0)) : L.starProjection x = x := by
  have hz : x - L.starProjection x = 0 := by
    apply hsep
    intro j
    have he : (fun i => inner ℝ (L.starProjection (e j)) (F i - x)) =ᶠ[l]
        (fun _ => inner ℝ (e j) (x - L.starProjection x)) := by
      filter_upwards [hF, hhead j] with i hi hhi
      exact projected_observation_exact_defect L (e j) (F i) x hi hhi
    have hc : Tendsto (fun i => inner ℝ (L.starProjection (e j)) (F i - x))
        l (𝓝 (inner ℝ (e j) (x - L.starProjection x))) :=
      tendsto_const_nhds.congr' he.symm
    exact tendsto_nhds_unique hc (hint j)
  exact (sub_eq_zero.mp hz).symm


/-- The actual weak-star dual functional restricted to the complete subspace. -/
def restrictedDual (x : E) : WeakDual ℝ L :=
  StrongDual.toWeakDual ((innerSL ℝ x).comp L.subtypeL)

omit [CompleteSpace L] in
@[simp] theorem restrictedDual_apply (x : E) (v : L) :
    restrictedDual L x v = inner ℝ (v : E) x := by
  change inner ℝ x (v : E) = inner ℝ (v : E) x
  exact (real_inner_comm x (v : E)).symm

/-- The target and its projection define exactly the same restricted dual element. -/
theorem restrictedDual_projection (x : E) :
    restrictedDual L (L.starProjection x) = restrictedDual L x := by
  apply DFunLike.ext
  intro v
  simp only [restrictedDual_apply]
  rw [real_inner_comm (L.starProjection x) (v : E), real_inner_comm x (v : E)]
  exact projected_test_on_mem L x (v : E) v.property

omit [CompleteSpace L] in
/-- Genuine weak-star convergence supplies every internal test, including
projected point observations that need not be finite combinations of atoms. -/
theorem internal_tests_of_restricted_weakStar {l : Filter I}
    (F : I → E) (x : E)
    (ht : Tendsto (fun i => restrictedDual L (F i)) l (𝓝 (restrictedDual L x))) :
    ∀ v : E, v ∈ L →
      Tendsto (fun i => inner ℝ v (F i)) l (𝓝 (inner ℝ v x)) := by
  intro v hv
  have h := ((WeakDual.eval_continuous (⟨v, hv⟩ : L)).tendsto (restrictedDual L x)).comp ht
  simpa only [Function.comp_def, restrictedDual_apply] using h

end RiemannResearch.Analysis.ProjectedObservationTests
