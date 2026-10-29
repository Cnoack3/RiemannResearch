/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QExactHeadOptimizerComparison
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.Analysis.AffineEnergyMinimum
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel

/-! Explicit Q/P affine energy minimizers, preserving the physical sequence.
Source: orthogonal projection onto the common zero-head tangent space. -/
noncomputable section
namespace RiemannResearch.RH.QAffineEnergyMinimizers
open ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open QExactHeadOptimizerComparison
open RiemannResearch.Analysis.AffineEnergyMinimum

def qMin (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : QHilbert) : QHilbert := C - U.starProjection C

def pMin (U : Submodule ℝ QHilbert)
    [(U.map toParetoLinear).HasOrthogonalProjection]
    (C : QHilbert) : QHilbert :=
  toQ (toPareto C - (U.map toParetoLinear).starProjection (toPareto C))

theorem base_sub_qMin_mem (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : QHilbert) : C - qMin U C ∈ U := by
  have he : C - qMin U C = U.starProjection C := by unfold qMin; abel
  rw [he]
  exact U.starProjection_apply_mem C

theorem toPareto_pMin (U : Submodule ℝ QHilbert)
    [(U.map toParetoLinear).HasOrthogonalProjection] (C : QHilbert) :
    toPareto (pMin U C) =
      toPareto C - (U.map toParetoLinear).starProjection (toPareto C) := by
  simp only [pMin, toPareto_toQ]

theorem pMin_sub_base_mem (U : Submodule ℝ QHilbert)
    [(U.map toParetoLinear).HasOrthogonalProjection] (C : QHilbert) :
    pMin U C - C ∈ U := by
  obtain ⟨u, hu, he⟩ := (U.map toParetoLinear).starProjection_apply_mem (toPareto C)
  have hp : pMin U C = C - u := by
    unfold pMin
    rw [← he]
    change toQLinear (toParetoLinear C - toParetoLinear u) = C - u
    rw [map_sub]
    change toQ (toPareto C) - toQ (toPareto u) = C - u
    rw [toQ_toPareto, toQ_toPareto]
  rw [hp]
  have hneg : (C - u) - C = -u := by abel
  rw [hneg]
  exact U.neg_mem hu

theorem pMin_sub_qMin_mem (U : Submodule ℝ QHilbert)
    [U.HasOrthogonalProjection] [(U.map toParetoLinear).HasOrthogonalProjection]
    (C : QHilbert) : pMin U C - qMin U C ∈ U := by
  have he : pMin U C - qMin U C = (pMin U C - C) + (C - qMin U C) := by abel
  rw [he]
  exact U.add_mem (pMin_sub_base_mem U C) (base_sub_qMin_mem U C)

theorem qMin_minimizes (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : QHilbert) : ∀ u ∈ U, ‖qMin U C‖ ^ 2 ≤ ‖qMin U C + u‖ ^ 2 := by
  apply (minimum_iff_normal U (qMin U C)).mpr
  intro u hu
  exact Submodule.inner_right_of_mem_orthogonal hu
    (Submodule.sub_starProjection_mem_orthogonal (K := U) C)

theorem pMin_minimizes (U : Submodule ℝ QHilbert)
    [(U.map toParetoLinear).HasOrthogonalProjection] (C : QHilbert) :
    ∀ u ∈ U, ‖toPareto (pMin U C)‖ ^ 2 ≤ ‖toPareto (pMin U C + u)‖ ^ 2 := by
  intro u hu
  have hpu : toPareto u ∈ U.map toParetoLinear := ⟨u, hu, rfl⟩
  have horth : inner ℝ (toPareto u) (toPareto (pMin U C)) = 0 := by
    rw [toPareto_pMin]
    exact Submodule.inner_right_of_mem_orthogonal hpu
      (Submodule.sub_starProjection_mem_orthogonal (K := U.map toParetoLinear) (toPareto C))
  change ‖toPareto (pMin U C)‖ ^ 2 ≤ ‖toParetoLinear (pMin U C + u)‖ ^ 2
  rw [map_add]
  change ‖toPareto (pMin U C)‖ ^ 2 ≤ ‖toPareto (pMin U C) + toPareto u‖ ^ 2
  rw [norm_add_sq_real, real_inner_comm, horth]
  nlinarith [sq_nonneg ‖toPareto u‖]

theorem actual_minimizers_sharp_bound
    (H : ℕ) (U : Submodule ℝ QHilbert)
    [U.HasOrthogonalProjection] [(U.map toParetoLinear).HasOrthogonalProjection]
    (C : QHilbert) (hU : ∀ u ∈ U, ∀ n < H, u n = 0) :
    4 * ((H : ℝ) + 1) * ((H : ℝ) + 2) * ‖pMin U C - qMin U C‖ ^ 2 ≤
      ‖qMin U C - QFiniteSupportDualCriterion.finiteHead H (qMin U C)‖ ^ 2 :=
  affine_minimizers_sharp_bound H U _ _ hU (pMin_sub_qMin_mem U C)
    (qMin_minimizes U C) (pMin_minimizes U C)

theorem actual_minimizers_competitor_bound
    (H : ℕ) (U : Submodule ℝ QHilbert)
    [U.HasOrthogonalProjection] [(U.map toParetoLinear).HasOrthogonalProjection]
    (C : QHilbert) (hU : ∀ u ∈ U, ∀ n < H, u n = 0) :
    4 * ((H : ℝ) + 1) * ((H : ℝ) + 2) * ‖pMin U C - qMin U C‖ ^ 2 ≤ ‖C‖ ^ 2 :=
  affine_minimizers_bound_of_competitor H U _ _ C hU (pMin_sub_qMin_mem U C)
    (base_sub_qMin_mem U C) (qMin_minimizes U C) (pMin_minimizes U C)

end RiemannResearch.RH.QAffineEnergyMinimizers
