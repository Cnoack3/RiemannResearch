/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.AffineEnergyMinimum
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact enlargement and extension of affine energy minima

Source: user-provided minimum-energy optimizer agenda, 29 October 2026,
Section 6 (the statement and proof strategy).

The space `K` is the zero-old-head tangent in the enlarged dictionary,
and `N ≤ K` is the zero-new-head tangent.  The assumption `G - F ∈ K`
expresses that the old vector and a new feasible vector have the same old
head.  No independence of coordinate constraints is required.

These Hilbert identities have no arithmetic boundedness premise.  The
application still needs an estimate on cumulative extension costs minus
enlargement gains.
-/

noncomputable section
namespace RiemannResearch.Analysis.AffineEnergyTransition

open AffineEnergyMinimum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The minimum-energy vector in the affine translate `C + U`. -/
def minimumOff (U : Submodule ℝ E) [U.HasOrthogonalProjection] (C : E) : E :=
  C - U.starProjection C

theorem minimumOff_normal (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (C : E) : ∀ u ∈ U, inner ℝ u (minimumOff U C) = 0 := by
  intro u hu
  exact Submodule.inner_right_of_mem_orthogonal hu
    (Submodule.sub_starProjection_mem_orthogonal (K := U) C)

theorem minimumOff_minimizes (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (C : E) : ∀ u ∈ U, ‖minimumOff U C‖ ^ 2 ≤ ‖minimumOff U C + u‖ ^ 2 :=
  (minimum_iff_normal U (minimumOff U C)).mpr (minimumOff_normal U C)

/-- Normal equations determine the affine minimizer uniquely. -/
theorem normal_unique (U : Submodule ℝ E) {x y : E}
    (hx : ∀ u ∈ U, inner ℝ u x = 0)
    (hy : ∀ u ∈ U, inner ℝ u y = 0) (hxy : x - y ∈ U) : x = y := by
  have hi : inner ℝ (x - y) (x - y) = 0 := by
    rw [inner_sub_right, hx _ hxy, hy _ hxy, sub_self]
  have hn : ‖x - y‖ ^ 2 = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using hi
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

theorem minimumOff_unique (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (C x : E) (hmem : x - C ∈ U)
    (hnormal : ∀ u ∈ U, inner ℝ u x = 0) : x = minimumOff U C := by
  apply normal_unique U hnormal (minimumOff_normal U C)
  have he : x - minimumOff U C = (x - C) + U.starProjection C := by
    unfold minimumOff
    abel
  rw [he]
  exact U.add_mem hmem (U.starProjection_apply_mem C)

/-- Every affine competitor has the minimum energy plus an exact square. -/
theorem minimumOff_completion (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (C x : E) (hmem : x - C ∈ U) :
    ‖x‖ ^ 2 = ‖minimumOff U C‖ ^ 2 + ‖x - minimumOff U C‖ ^ 2 := by
  have hd : x - minimumOff U C ∈ U := by
    have he : x - minimumOff U C = (x - C) + U.starProjection C := by
      unfold minimumOff
      abel
    rw [he]
    exact U.add_mem hmem (U.starProjection_apply_mem C)
  have ho := minimumOff_normal U C _ hd
  have he : x = minimumOff U C + (x - minimumOff U C) := by abel
  calc
    ‖x‖ ^ 2 = ‖minimumOff U C + (x - minimumOff U C)‖ ^ 2 :=
      congrArg (fun z : E => ‖z‖ ^ 2) he
    _ = _ := by rw [norm_add_sq_real, real_inner_comm, ho]; ring

/-- Enlarging the tangent saves exactly the projected energy. -/
theorem enlargement_energy (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (F : E) :
    ‖F‖ ^ 2 = ‖minimumOff K F‖ ^ 2 + ‖K.starProjection F‖ ^ 2 := by
  have he : F - minimumOff K F = K.starProjection F := by
    unfold minimumOff
    abel
  simpa only [he] using minimumOff_completion K F F (by simp)

/-- Energy accounting holds for every vector retaining the old head. -/
theorem feasible_energy_transition (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (F G : E) (hGF : G - F ∈ K) :
    ‖G‖ ^ 2 - ‖F‖ ^ 2 =
      ‖G - minimumOff K F‖ ^ 2 - ‖K.starProjection F‖ ^ 2 := by
  have hnew := minimumOff_completion K F G hGF
  have hold := enlargement_energy K F
  linarith

/-- The signed correction retains the cross term exactly. -/
theorem signed_correction_energy (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (F s : E) (hs : s ∈ K) :
    2 * inner ℝ F (s - K.starProjection F) + ‖s - K.starProjection F‖ ^ 2 =
      ‖s‖ ^ 2 - ‖K.starProjection F‖ ^ 2 := by
  have hmem : (F + (s - K.starProjection F)) - F ∈ K := by
    have he : (F + (s - K.starProjection F)) - F = s - K.starProjection F := by
      abel
    rw [he]
    exact K.sub_mem hs (K.starProjection_apply_mem F)
  have he : F + (s - K.starProjection F) - minimumOff K F = s := by
    unfold minimumOff
    abel
  have h := feasible_energy_transition K F (F + (s - K.starProjection F)) hmem
  rw [he, norm_add_sq_real] at h
  linarith

/-- Least-norm correction after the old head is reoptimized. -/
def extension (K N : Submodule ℝ E)
    [K.HasOrthogonalProjection] [N.HasOrthogonalProjection] (F G : E) : E :=
  minimumOff N (G - minimumOff K F)

theorem extension_mem (K N : Submodule ℝ E)
    [K.HasOrthogonalProjection] [N.HasOrthogonalProjection] (hNK : N ≤ K)
    (F G : E) (hGF : G - F ∈ K) : extension K N F G ∈ K := by
  have hbase : G - minimumOff K F ∈ K := by
    have he : G - minimumOff K F = (G - F) + K.starProjection F := by
      unfold minimumOff
      abel
    rw [he]
    exact K.add_mem hGF (K.starProjection_apply_mem F)
  exact K.sub_mem hbase (hNK (N.starProjection_apply_mem (G - minimumOff K F)))

theorem extension_normal (K N : Submodule ℝ E)
    [K.HasOrthogonalProjection] [N.HasOrthogonalProjection] (F G : E) :
    ∀ u ∈ N, inner ℝ u (extension K N F G) = 0 :=
  minimumOff_normal N (G - minimumOff K F)

theorem extension_minimizes (K N : Submodule ℝ E)
    [K.HasOrthogonalProjection] [N.HasOrthogonalProjection] (F G : E) :
    ∀ u ∈ N, ‖extension K N F G‖ ^ 2 ≤ ‖extension K N F G + u‖ ^ 2 :=
  minimumOff_minimizes N (G - minimumOff K F)

/-- The correction retains precisely the prescribed new-head affine class. -/
theorem extension_sub_base_mem (K N : Submodule ℝ E)
    [K.HasOrthogonalProjection] [N.HasOrthogonalProjection] (F G : E) :
    extension K N F G - (G - minimumOff K F) ∈ N := by
  have he : extension K N F G - (G - minimumOff K F) =
      -N.starProjection (G - minimumOff K F) := by
    unfold extension minimumOff
    abel
  rw [he]
  exact N.neg_mem (N.starProjection_apply_mem _)

/-- Exact enlargement/extension decomposition of the new affine minimizer. -/
theorem minimumOff_decomposition (K N : Submodule ℝ E)
    [K.HasOrthogonalProjection] [N.HasOrthogonalProjection] (hNK : N ≤ K)
    (F G : E) :
    minimumOff N G = minimumOff K F + extension K N F G := by
  symm
  apply minimumOff_unique N G
  · have he : minimumOff K F + extension K N F G - G =
        extension K N F G - (G - minimumOff K F) := by abel
    rw [he]
    exact extension_sub_base_mem K N F G
  · intro u hu
    rw [inner_add_right, minimumOff_normal K F u (hNK hu),
      extension_normal K N F G u hu, add_zero]

/-- Complete signed transition identity.  Both square terms are retained. -/
theorem energy_transition (K N : Submodule ℝ E)
    [K.HasOrthogonalProjection] [N.HasOrthogonalProjection] (hNK : N ≤ K)
    (F G : E) (hGF : G - F ∈ K) :
    ‖minimumOff N G‖ ^ 2 - ‖F‖ ^ 2 =
      ‖extension K N F G‖ ^ 2 - ‖K.starProjection F‖ ^ 2 := by
  have ho := minimumOff_normal K F _ (extension_mem K N hNK F G hGF)
  have hnew : ‖minimumOff N G‖ ^ 2 =
      ‖minimumOff K F‖ ^ 2 + ‖extension K N F G‖ ^ 2 := by
    rw [minimumOff_decomposition K N hNK F G, norm_add_sq_real,
      real_inner_comm, ho]
    ring
  have hold := enlargement_energy K F
  linarith

end RiemannResearch.Analysis.AffineEnergyTransition
