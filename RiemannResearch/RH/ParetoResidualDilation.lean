/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoFirstHeadDefect
import RiemannResearch.Analysis.ContractiveNeumannReconstruction

/-!
# Compressed dilations reconstruct the actual Pareto obstruction

Source: independently developed continuation of the user's Projection Defect
and All Annihilators handoff, 2026-09-22. No novelty is claimed.
The actual compressed integer dilations form a semigroup. The first-head
defect reconstructs the constant-target residual with a geometric error,
and its full compressed orbit separates the entire arithmetic annihilator.
These statements do not force either residual to vanish and do not prove RH.
-/
noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Compression of the unscaled integer dilation to the arithmetic annihilator space. -/
def residualDilation (B : ℕ) (hB : 0 < B) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  closedSpaceᗮ.starProjection.comp
    (((B : ℝ)⁻¹) • hilbertDilationContinuous B hB)

theorem residualDilation_apply (B : ℕ) (hB : 0 < B) (x : ThresholdHilbert) :
    residualDilation B hB x =
      closedSpaceᗮ.starProjection (((B : ℝ)⁻¹) • hilbertDilation B hB x) := rfl

theorem residualDilation_mem_orthogonal (B : ℕ) (hB : 0 < B)
    (x : ThresholdHilbert) : residualDilation B hB x ∈ closedSpaceᗮ :=
  closedSpaceᗮ.starProjection_apply_mem _

theorem residualDilation_eq_zero_of_mem (B : ℕ) (hB : 0 < B)
    {x : ThresholdHilbert} (hx : x ∈ closedSpace) :
    residualDilation B hB x = 0 := by
  rw [residualDilation_apply, Submodule.starProjection_orthogonal]
  change _ - closedSpace.starProjection _ = 0
  exact sub_eq_zero.mpr (Submodule.starProjection_eq_self_iff.mpr
    (closedSpace.smul_mem _ (closedSpace_dilation hx B hB))).symm

theorem residualDilation_complement (B : ℕ) (hB : 0 < B) (x : ThresholdHilbert) :
    residualDilation B hB (closedSpaceᗮ.starProjection x) =
      residualDilation B hB x := by
  rw [Submodule.starProjection_orthogonal]
  change residualDilation B hB (x - closedSpace.starProjection x) = _
  rw [map_sub, residualDilation_eq_zero_of_mem B hB
    (closedSpace.starProjection_apply_mem x), sub_zero]

theorem residualDilation_norm_sq_le (B : ℕ) (hB : 0 < B)
    (x : ThresholdHilbert) :
    ‖residualDilation B hB x‖ ^ 2 ≤ (B : ℝ)⁻¹ * ‖x‖ ^ 2 := by
  rw [residualDilation_apply]
  have h := Submodule.norm_starProjection_apply_le closedSpaceᗮ
    (((B : ℝ)⁻¹) • hilbertDilation B hB x)
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  calc
    _ ≤ ‖((B : ℝ)⁻¹) • hilbertDilation B hB x‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    _ = _ := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hilbertDilation_norm_sq]
      field_simp

theorem residualDilation_comp (B C : ℕ) (hB : 0 < B) (hC : 0 < C)
    (x : ThresholdHilbert) :
    residualDilation B hB (residualDilation C hC x) =
      residualDilation (B * C) (Nat.mul_pos hB hC) x := by
  rw [residualDilation_apply C hC, residualDilation_complement, map_smul]
  rw [residualDilation_apply, residualDilation_apply]
  rw [hilbertDilation_comp]
  rw [← map_smul, smul_smul]
  congr 2
  push_cast
  rw [mul_inv_rev]

theorem orthogonalProjection_one :
    closedSpaceᗮ.starProjection hilbertOne = limitResidual := by
  rw [Submodule.starProjection_orthogonal]
  rfl

theorem orthogonalProjection_firstHead :
    closedSpaceᗮ.starProjection (finiteHeadIndicator 1) = firstHeadResidual := by
  rw [Submodule.starProjection_orthogonal]
  rfl

theorem firstHeadResidual_eq_sub_residualDilation :
    firstHeadResidual = limitResidual -
      residualDilation 2 (by omega) limitResidual := by
  have h := congrArg (fun x => closedSpaceᗮ.starProjection x)
    (finiteHeadIndicator_eq_dilation_difference 1)
  rw [map_sub, orthogonalProjection_firstHead, orthogonalProjection_one] at h
  have hc := residualDilation_complement 2 (by omega) hilbertOne
  rw [orthogonalProjection_one] at hc
  rw [hc]
  simpa only [residualDilation_apply, Nat.reduceAdd, Nat.cast_ofNat] using h

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem residualDilation_one (x : ThresholdHilbert) :
    residualDilation 1 (by omega) x = closedSpaceᗮ.starProjection x := by
  simp [residualDilation_apply, hilbertDilation_one]

theorem firstHeadResidual_reconstruction (M : ℕ) :
    limitResidual - ∑ j ∈ Finset.range M,
      (residualDilation 2 (by omega) ^ j) firstHeadResidual =
        (residualDilation 2 (by omega) ^ M) limitResidual :=
  ContinuousLinearMap.finite_neumann_reconstruction _ _ _
    firstHeadResidual_eq_sub_residualDilation M

theorem firstHeadResidual_reconstruction_error_sq (M : ℕ) :
    ‖limitResidual - ∑ j ∈ Finset.range M,
      (residualDilation 2 (by omega) ^ j) firstHeadResidual‖ ^ 2 ≤
        (1 / 2 : ℝ) ^ M * limitEnergy := by
  apply ContinuousLinearMap.neumann_reconstruction_error_sq _ _ (by norm_num)
    _ _ _ firstHeadResidual_eq_sub_residualDilation
  intro z
  simpa using residualDilation_norm_sq_le 2 (by omega) z

theorem firstHeadResidual_reconstruction_tendsto :
    Tendsto (fun M => ∑ j ∈ Finset.range M,
      (residualDilation 2 (by omega) ^ j) firstHeadResidual) atTop (𝓝 limitResidual) := by
  apply ContinuousLinearMap.tendsto_neumann_reconstruction _ (1 / 2)
    (by norm_num) (by norm_num) _ _ _ firstHeadResidual_eq_sub_residualDilation
  intro z
  simpa using residualDilation_norm_sq_le 2 (by omega) z

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem inner_orthogonalProjection_right (z : ThresholdHilbert)
    (hz : z ∈ closedSpaceᗮ) (x : ThresholdHilbert) :
    inner ℝ z (closedSpaceᗮ.starProjection x) = inner ℝ z x := by
  have ho : inner ℝ z (closedSpace.starProjection x) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp hz _
      (closedSpace.starProjection_apply_mem x)
  rw [Submodule.starProjection_orthogonal]
  change inner ℝ z (x - closedSpace.starProjection x) = _
  rw [inner_sub_right, ho, sub_zero]

/-- The compressed integer dilations of the first-head defect separate the
entire arithmetic annihilator space. -/
theorem annihilator_eq_zero_of_inner_firstHead_orbit_zero
    (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ)
    (horbit : ∀ B : ℕ, ∀ hB : 0 < B,
      inner ℝ z (residualDilation B hB firstHeadResidual) = 0) :
    z = 0 := by
  have hpow (j : ℕ) : ∀ B : ℕ, ∀ hB : 0 < B,
      inner ℝ z (residualDilation B hB
        ((residualDilation 2 (by omega) ^ j) firstHeadResidual)) = 0 := by
    induction j with
    | zero =>
        intro B hB
        simpa using horbit B hB
    | succ j ih =>
        intro B hB
        rw [pow_succ' (residualDilation 2 (by omega)) j,
          mul_apply_eq_comp, residualDilation_comp]
        exact ih (B * 2) (by positivity)
  have hpair (B : ℕ) (hB : 0 < B) :
      inner ℝ z (residualDilation B hB limitResidual) = 0 := by
    have hfinite (M : ℕ) :
        inner ℝ z (residualDilation B hB
          (∑ j ∈ Finset.range M,
            (residualDilation 2 (by omega) ^ j) firstHeadResidual)) = 0 := by
      rw [map_sum, inner_sum]
      exact Finset.sum_eq_zero (fun j _ => hpow j B hB)
    have hc : Continuous (fun x : ThresholdHilbert =>
        inner ℝ z (residualDilation B hB x)) :=
      continuous_const.inner (residualDilation B hB).continuous
    have hl := (hc.tendsto limitResidual).comp firstHeadResidual_reconstruction_tendsto
    have he : (fun M : ℕ => inner ℝ z (residualDilation B hB
          (∑ j ∈ Finset.range M,
            (residualDilation 2 (by omega) ^ j) firstHeadResidual))) =
        (fun _ : ℕ => (0 : ℝ)) := funext hfinite
    simp only [Function.comp_def] at hl
    rw [he] at hl
    exact tendsto_nhds_unique hl tendsto_const_nhds
  apply eq_zero_of_inner_dilation_one_eq_zero z
  intro B hB
  have hh := hpair B hB
  rw [← orthogonalProjection_one, residualDilation_complement,
    residualDilation_apply, inner_orthogonalProjection_right z hz,
    inner_smul_right] at hh
  exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (by exact_mod_cast (Nat.ne_of_gt hB)))

end RiemannResearch.RH.Pareto.CoefficientStabilization
