/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel

/-!
# Orthogonal splitting of nested prime and squarefree spaces

This file isolates the Hilbert-space argument behind the prime/carry split.
For closed subspaces `W ≤ V`, the canonical carry space is `V ⊓ Wᗮ`.
Its projection is the difference of the two nested projections.

The convergence theorem applies to increasing finite prime and squarefree
spaces. Their carry spaces need not form an increasing sequence.

Source: the prime/carry decomposition in
*Projection Displacement, Prime Atoms, and Carries*, 5 November 2026,
page 3. Mathlib supplies the underlying orthogonal-projection theorem and
monotone strong convergence theorem.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.NestedOrthogonalDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {W V : Submodule ℝ E}
variable [W.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Applying the smaller projection after the larger projection has no effect. -/
theorem nested_projection_apply (hWV : W ≤ V) (x : E) :
    W.starProjection (V.starProjection x) = W.starProjection x := by
  simpa only [ContinuousLinearMap.comp_apply] using
    congrArg (fun T : E →L[ℝ] E => T x)
      (Submodule.starProjection_comp_starProjection_of_le hWV)

/-- The difference of nested projections belongs to the canonical carry space. -/
theorem projection_difference_mem (hWV : W ≤ V) (x : E) :
    V.starProjection x - W.starProjection x ∈ V ⊓ Wᗮ := by
  constructor
  · exact V.sub_mem (V.starProjection_apply_mem x)
      (hWV (W.starProjection_apply_mem x))
  · change V.starProjection x - W.starProjection x ∈ Wᗮ
    simpa only [nested_projection_apply hWV x] using
      (Submodule.sub_starProjection_mem_orthogonal
        (K := W) (V.starProjection x))

/-- The remaining part is orthogonal to the canonical carry space. -/
theorem sub_projection_difference_mem_orthogonal (x : E) :
    x - (V.starProjection x - W.starProjection x) ∈ (V ⊓ Wᗮ)ᗮ := by
  intro z hz
  have hV : inner ℝ z (x - V.starProjection x) = 0 :=
    (Submodule.sub_starProjection_mem_orthogonal (K := V) x) z hz.1
  have hW : inner ℝ z (W.starProjection x) = 0 :=
    inner_eq_zero_symm.mp (hz.2 _ (W.starProjection_apply_mem x))
  rw [show x - (V.starProjection x - W.starProjection x) =
    (x - V.starProjection x) + W.starProjection x by abel,
    inner_add_right, hV, hW, add_zero]

/-- The nested carry space admits an orthogonal projection. -/
theorem carry_hasOrthogonalProjection (hWV : W ≤ V) :
    (V ⊓ Wᗮ).HasOrthogonalProjection where
  exists_orthogonal x :=
    ⟨V.starProjection x - W.starProjection x,
      projection_difference_mem hWV x,
      sub_projection_difference_mem_orthogonal x⟩

section CarryProjection

variable [(V ⊓ Wᗮ).HasOrthogonalProjection]

/-- Exact projection onto the orthogonal carry component. -/
theorem carry_projection_apply (hWV : W ≤ V) (x : E) :
    (V ⊓ Wᗮ).starProjection x =
      V.starProjection x - W.starProjection x := by
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (projection_difference_mem hWV x)
    (sub_projection_difference_mem_orthogonal x)

/-- The operator form of the prime/carry decomposition. -/
theorem carry_projection (hWV : W ≤ V) :
    (V ⊓ Wᗮ).starProjection = V.starProjection - W.starProjection := by
  ext x
  exact carry_projection_apply hWV x

/-- A legal vector splits into its prime and carry components. -/
theorem projection_split_of_mem (hWV : W ≤ V) {x : E} (hx : x ∈ V) :
    W.starProjection x + (V ⊓ Wᗮ).starProjection x = x := by
  rw [carry_projection_apply hWV, V.starProjection_eq_self_iff.mpr hx]
  exact add_sub_cancel _ _

/-- Pythagoras for the prime and carry components of a legal vector. -/
theorem norm_sq_split_of_mem (hWV : W ≤ V) {x : E} (hx : x ∈ V) :
    ‖x‖ ^ 2 = ‖W.starProjection x‖ ^ 2 +
      ‖(V ⊓ Wᗮ).starProjection x‖ ^ 2 := by
  rw [carry_projection_apply hWV, V.starProjection_eq_self_iff.mpr hx]
  simpa only [Submodule.starProjection_orthogonal_val] using
    (Submodule.norm_sq_eq_add_norm_sq_starProjection x W)

end CarryProjection

omit [W.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- The canonical carry space is orthogonal to the prime space. -/
theorem prime_carry_inner_eq_zero {w c : E} (hw : w ∈ W)
    (hc : c ∈ V ⊓ Wᗮ) : inner ℝ w c = 0 :=
  hc.2 w hw

omit [V.HasOrthogonalProjection] in
/-- The two canonical components span the whole legal space. -/
theorem prime_sup_carry (hWV : W ≤ V) : W ⊔ (V ⊓ Wᗮ) = V := by
  simpa only [inf_comm] using
    (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hWV)

section FixedComponents

variable {ι : Type*} {l : Filter ι} {x : ι → E} {a : E}

/-- Any norm-convergent legal approximation has convergent prime components. -/
theorem prime_component_tendsto (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun i => W.starProjection (x i)) l (𝓝 (W.starProjection a)) :=
  (W.starProjection.continuous.tendsto a).comp hx

/-- Any norm-convergent approximation has convergent orthogonal components. -/
theorem orthogonal_component_tendsto (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun i => x i - W.starProjection (x i)) l
      (𝓝 (a - W.starProjection a)) :=
  hx.sub (prime_component_tendsto hx)

end FixedComponents

section FiniteStages

/-- Strong convergence of contractive projections also allows a convergent input. -/
theorem projection_moving_input_tendsto
    (Un : ℕ → Submodule ℝ E) [∀ n, (Un n).HasOrthogonalProjection]
    {xn : ℕ → E} {a b : E}
    (hx : Tendsto xn atTop (𝓝 a))
    (hfixed : Tendsto (fun n => (Un n).starProjection a) atTop (𝓝 b)) :
    Tendsto (fun n => (Un n).starProjection (xn n)) atTop (𝓝 b) := by
  have hzero : Tendsto
      (fun n => (Un n).starProjection (xn n - a)) atTop (𝓝 (0 : E)) := by
    apply squeeze_zero_norm
      (fun n => (Un n).norm_starProjection_apply_le (xn n - a))
    simpa only [sub_self, norm_zero] using
      (hx.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => a) atTop (𝓝 a))).norm
  simpa only [map_sub, sub_add_cancel, zero_add] using hzero.add hfixed

variable (Wn Vn : ℕ → Submodule ℝ E)
variable [∀ n, (Wn n).HasOrthogonalProjection]
variable [∀ n, (Vn n).HasOrthogonalProjection]
variable [∀ n, (Vn n ⊓ (Wn n)ᗮ).HasOrthogonalProjection]
variable [(V ⊓ Wᗮ).HasOrthogonalProjection]
variable [(⨆ n, Wn n).topologicalClosure.HasOrthogonalProjection]
variable [(⨆ n, Vn n).topologicalClosure.HasOrthogonalProjection]

/-- Finite carry projections converge strongly even when their ranges are not nested. -/
theorem finite_carry_projection_tendsto
    (hWV : W ≤ V) (hn : ∀ n, Wn n ≤ Vn n)
    (hWn : Monotone Wn) (hVn : Monotone Vn)
    (hW : (⨆ n, Wn n).topologicalClosure = W)
    (hV : (⨆ n, Vn n).topologicalClosure = V) (x : E) :
    Tendsto (fun n => (Vn n ⊓ (Wn n)ᗮ).starProjection x) atTop
      (𝓝 ((V ⊓ Wᗮ).starProjection x)) := by
  have tW := Submodule.starProjection_tendsto_closure_iSup Wn hWn x
  have tV := Submodule.starProjection_tendsto_closure_iSup Vn hVn x
  simp only [hW] at tW
  simp only [hV] at tV
  have hfun : (fun n => (Vn n ⊓ (Wn n)ᗮ).starProjection x) =
      (fun n => (Vn n).starProjection x - (Wn n).starProjection x) := by
    funext n
    exact carry_projection_apply (hn n) x
  rw [hfun, carry_projection_apply hWV]
  exact tV.sub tW

/-- The actual convergent finite displacements have convergent carry components. -/
theorem finite_carry_of_moving_input_tendsto
    (hWV : W ≤ V) (hn : ∀ n, Wn n ≤ Vn n)
    (hWn : Monotone Wn) (hVn : Monotone Vn)
    (hW : (⨆ n, Wn n).topologicalClosure = W)
    (hV : (⨆ n, Vn n).topologicalClosure = V)
    {xn : ℕ → E} {x : E} (hx : Tendsto xn atTop (𝓝 x)) :
    Tendsto (fun n => (Vn n ⊓ (Wn n)ᗮ).starProjection (xn n)) atTop
      (𝓝 ((V ⊓ Wᗮ).starProjection x)) := by
  exact projection_moving_input_tendsto
    (fun n => Vn n ⊓ (Wn n)ᗮ) hx
    (finite_carry_projection_tendsto Wn Vn hWV hn hWn hVn hW hV x)

end FiniteStages

end RiemannResearch.Analysis.NestedOrthogonalDecomposition

namespace RiemannResearch.Analysis.NestedOrthogonalDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {W V : Submodule ℝ E}
variable [W.HasOrthogonalProjection] [V.HasOrthogonalProjection]

omit [V.HasOrthogonalProjection] in
/-- Projecting the legal space orthogonally away from the prime space gives its carry space. -/
theorem orthogonal_map_eq_carry (hWV : W ≤ V) :
    V.map Wᗮ.starProjection.toLinearMap = V ⊓ Wᗮ := by
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    constructor
    · change Wᗮ.starProjection v ∈ V
      rw [Submodule.starProjection_orthogonal_val]
      exact V.sub_mem hv (hWV (W.starProjection_apply_mem v))
    · exact Wᗮ.starProjection_apply_mem v
  · intro x hx
    refine ⟨x, hx.1, ?_⟩
    exact Wᗮ.starProjection_eq_self_iff.mpr hx.2

omit [V.HasOrthogonalProjection] in
/-- The carry space is generated by the orthogonal parts of any legal generating set. -/
theorem carry_eq_closure_projected_generators
    [(V ⊓ Wᗮ).HasOrthogonalProjection]
    (hWV : W ≤ V) (S : Set E)
    (hV : (Submodule.span ℝ S).topologicalClosure = V) :
    V ⊓ Wᗮ =
      (Submodule.span ℝ (Wᗮ.starProjection '' S)).topologicalClosure := by
  have hmap := orthogonal_map_eq_carry hWV
  have hspan : (Submodule.span ℝ S).map Wᗮ.starProjection.toLinearMap =
      Submodule.span ℝ (Wᗮ.starProjection '' S) :=
    Submodule.map_span Wᗮ.starProjection.toLinearMap S
  have hSV : Submodule.span ℝ S ≤ V := by
    rw [← hV]
    exact (Submodule.span ℝ S).le_topologicalClosure
  have hclosed : IsClosed ((V ⊓ Wᗮ : Submodule ℝ E) : Set E) := by
    simpa only [Submodule.orthogonal_orthogonal] using
      (V ⊓ Wᗮ)ᗮ.isClosed_orthogonal
  apply le_antisymm
  · rw [← hmap, ← hV]
    simpa only [hspan] using
      (Submodule.topologicalClosure_map Wᗮ.starProjection (Submodule.span ℝ S))
  · apply (Submodule.span ℝ (Wᗮ.starProjection '' S)).topologicalClosure_minimal
        _ hclosed
    rw [← hspan, ← hmap]
    exact Submodule.map_mono hSV

end RiemannResearch.Analysis.NestedOrthogonalDecomposition
