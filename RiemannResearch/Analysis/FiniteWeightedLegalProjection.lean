/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedRefinement
import RiemannResearch.Analysis.AffineObservationProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
/-!
# Orthogonal projections for finite positive weights and feasible observations

Source: standard Hilbert projection transported by coordinate multiplication
by sqrt(w), applied to the user's directed legal weighted-CRT continuation,
2 November 2026. The exact target-error splitting reuses
SingleObservationProjection.affine_target_error_split. This module constructs
the weighted and affine projections; no rank, uniform bound, or RH hypothesis
is postulated. Arithmetic legality is an application submodule.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteWeightedLegalProjection
open FiniteWeightedRefinement SingleObservationProjection
variable {ι : Type*} [Fintype ι]
def weightEquiv (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun f := WithLp.toLp 2 (fun i => Real.sqrt (w i) * f i)
  invFun x := fun i => x i / Real.sqrt (w i)
  left_inv := by
    intro f
    funext i
    change Real.sqrt (w i) * f i / Real.sqrt (w i) = f i
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hw i))]
  right_inv := by
    intro x
    ext i
    change Real.sqrt (w i) * (x i / Real.sqrt (w i)) = x i
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hw i))]
  map_add' := by
    intro f g
    ext i
    change Real.sqrt (w i) * (f i + g i) =
      Real.sqrt (w i) * f i + Real.sqrt (w i) * g i
    ring
  map_smul' := by
    intro c f
    ext i
    change Real.sqrt (w i) * (c * f i) = c * (Real.sqrt (w i) * f i)
    ring
theorem weightEquiv_norm_sq (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (f : ι → ℝ) : ‖weightEquiv w hw f‖ ^ 2 = energy w f := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold energy
  apply Finset.sum_congr rfl
  intro i _
  change ‖Real.sqrt (w i) * f i‖ ^ 2 = w i * f i ^ 2
  rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hw i).le]
def weightedProjection (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (S : Submodule ℝ (ι → ℝ)) (f : ι → ℝ) : ι → ℝ :=
  (weightEquiv w hw).symm
    ((S.map (weightEquiv w hw).toLinearMap).starProjection (weightEquiv w hw f))
theorem weightedProjection_mem (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (S : Submodule ℝ (ι → ℝ)) (f : ι → ℝ) :
    weightedProjection w hw S f ∈ S := by
  have h := (S.map (weightEquiv w hw).toLinearMap).starProjection_apply_mem
    (weightEquiv w hw f)
  obtain ⟨r, hr, he⟩ := h
  have hp : weightedProjection w hw S f = r := by
    unfold weightedProjection
    rw [← he]
    exact (weightEquiv w hw).symm_apply_apply r
  rw [hp]
  exact hr
theorem weightedProjection_completion (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (S : Submodule ℝ (ι → ℝ)) (f r : ι → ℝ) (hr : r ∈ S) :
    energy w (f-r) = energy w (f-weightedProjection w hw S f) +
      energy w (r-weightedProjection w hw S f) := by
  let e := weightEquiv w hw
  let U := S.map e.toLinearMap
  have her : e r ∈ U := ⟨r, hr, rfl⟩
  have he := affine_target_error_split U (e f) (e r) her
  have hp : e (weightedProjection w hw S f) = U.starProjection (e f) :=
    e.apply_symm_apply _
  have he1 : e (f-r) = e f-e r := e.map_sub f r
  have he2 : e (f-weightedProjection w hw S f) =
      e f-e (weightedProjection w hw S f) := e.map_sub f _
  have he3 : e (r-weightedProjection w hw S f) =
      e r-e (weightedProjection w hw S f) := e.map_sub r _
  rw [← hp, ← he1, ← he2, ← he3] at he
  simpa only [e, weightEquiv_norm_sq] using he
theorem weightedProjection_minimizes (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (S : Submodule ℝ (ι → ℝ)) (f r : ι → ℝ) (hr : r ∈ S) :
    energy w (f-weightedProjection w hw S f) ≤ energy w (f-r) := by
  rw [weightedProjection_completion w hw S f r hr]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hw i).le (sq_nonneg _)))
def constrainedProjection {K : Type*} [AddCommGroup K] [Module ℝ K]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (S : Submodule ℝ (ι → ℝ))
    (T : (ι → ℝ) →ₗ[ℝ] K) (r0 f : ι → ℝ) : ι → ℝ :=
  r0 + weightedProjection w hw (S ⊓ T.ker) (f-r0)
theorem constrainedProjection_mem {K : Type*} [AddCommGroup K] [Module ℝ K]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (S : Submodule ℝ (ι → ℝ))
    (T : (ι → ℝ) →ₗ[ℝ] K) (r0 f : ι → ℝ) (h0 : r0 ∈ S) :
    constrainedProjection w hw S T r0 f ∈ S := by
  exact S.add_mem h0 (weightedProjection_mem w hw (S ⊓ T.ker) (f-r0)).1
theorem constrainedProjection_observation {K : Type*} [AddCommGroup K] [Module ℝ K]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (S : Submodule ℝ (ι → ℝ))
    (T : (ι → ℝ) →ₗ[ℝ] K) (r0 f : ι → ℝ) :
    T (constrainedProjection w hw S T r0 f) = T r0 := by
  have h := (weightedProjection_mem w hw (S ⊓ T.ker) (f-r0)).2
  change T (weightedProjection w hw (S ⊓ T.ker) (f-r0)) = 0 at h
  rw [constrainedProjection, T.map_add, h, add_zero]
theorem constrainedProjection_completion {K : Type*} [AddCommGroup K] [Module ℝ K]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (S : Submodule ℝ (ι → ℝ))
    (T : (ι → ℝ) →ₗ[ℝ] K) (r0 f r : ι → ℝ)
    (h0 : r0 ∈ S) (hr : r ∈ S) (hT : T r = T r0) :
    energy w (f-r) = energy w (f-constrainedProjection w hw S T r0 f) +
      energy w (r-constrainedProjection w hw S T r0 f) := by
  have hd : r-r0 ∈ S ⊓ T.ker := by
    refine ⟨S.sub_mem hr h0, ?_⟩
    change T (r-r0) = 0
    rw [map_sub, hT, sub_self]
  have he := weightedProjection_completion w hw (S ⊓ T.ker) (f-r0) (r-r0) hd
  have h1 : (f-r0)-(r-r0) = f-r := by abel
  have h2 : (f-r0)-weightedProjection w hw (S ⊓ T.ker) (f-r0) =
      f-constrainedProjection w hw S T r0 f := by
    unfold constrainedProjection
    abel
  have h3 : (r-r0)-weightedProjection w hw (S ⊓ T.ker) (f-r0) =
      r-constrainedProjection w hw S T r0 f := by
    unfold constrainedProjection
    abel
  rwa [h1,h2,h3] at he
end RiemannResearch.Analysis.FiniteWeightedLegalProjection
