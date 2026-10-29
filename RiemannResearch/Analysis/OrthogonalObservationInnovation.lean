/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Observation energy after removing an old subspace

Source: independently developed from the user-provided moving-prediction
cancellation agenda, 29 October 2026. The concrete consumer is
RH/QCRTInnovationGain. Exact completions retain the norm-square remainder,
including the zero observation-vector case. No asymptotic input is assumed.
-/

namespace RiemannResearch.Analysis.OrthogonalObservationInnovation
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem observation_completion (x k : H) :
    ‖x‖ ^ 2 = (inner ℝ x k) ^ 2 / ‖k‖ ^ 2 +
      ‖x - (inner ℝ x k / ‖k‖ ^ 2) • k‖ ^ 2 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hn : ‖k‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hk)
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_smul_right]
    field_simp
    ring

variable (U : Submodule ℝ H) [CompleteSpace U]

def innovation (k : H) : H := k - U.starProjection k

theorem innovation_energy (k : H) :
    ‖innovation U k‖ ^ 2 = ‖k‖ ^ 2 - ‖U.starProjection k‖ ^ 2 := by
  have ho := Submodule.starProjection_inner_eq_zero k
    (U.starProjection k) (U.starProjection_apply_mem k)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  rw [innovation, norm_sub_sq_real]
  linarith

theorem innovation_inner (x k : H)
    (hx : ∀ u ∈ U, inner ℝ x u = 0) :
    inner ℝ x (innovation U k) = inner ℝ x k := by
  rw [innovation, inner_sub_right, hx _ (U.starProjection_apply_mem k), sub_zero]

theorem innovation_completion (x k : H)
    (hx : ∀ u ∈ U, inner ℝ x u = 0) :
    ‖x‖ ^ 2 = (inner ℝ x k) ^ 2 / ‖innovation U k‖ ^ 2 +
      ‖x - (inner ℝ x k / ‖innovation U k‖ ^ 2) • innovation U k‖ ^ 2 := by
  simpa only [innovation_inner U x k hx] using
    observation_completion x (innovation U k)

theorem innovation_source_sq_le (x k : H)
    (hx : ∀ u ∈ U, inner ℝ x u = 0) :
    (inner ℝ x k) ^ 2 ≤ ‖innovation U k‖ ^ 2 * ‖x‖ ^ 2 := by
  have h := real_inner_mul_inner_self_le x (innovation U k)
  rw [innovation_inner U x k hx, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at h
  nlinarith

theorem refined_transition_algebra (a b K c : ℝ) (hK : K ≠ 0)
    (hc : c = 0 → b = a) :
    b ^ 2 / K - (b - a) ^ 2 / c =
      (a * (2 * b - a) - (K - c) / c * (b - a) ^ 2) / K := by
  by_cases hcz : c = 0
  · rw [hc hcz, hcz]
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0),
      div_zero, zero_mul, sub_zero]
    ring
  · field_simp
    ring

/-- Changing representatives by an old direction does not change the innovation. -/
theorem innovation_eq_of_sub_mem (x y : H) (hxy : x - y ∈ U) :
    innovation U x = innovation U y := by
  have h := Submodule.starProjection_eq_self_iff.mpr hxy
  rw [map_sub] at h
  unfold innovation
  rw [← sub_eq_zero]
  calc
    x - U.starProjection x - (y - U.starProjection y) =
        (x - y) - (U.starProjection x - U.starProjection y) := by abel
    _ = 0 := by rw [h, sub_self]

theorem innovation_energy_le (x : H) : ‖innovation U x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [innovation_energy]
  exact sub_le_self _ (sq_nonneg _)

theorem old_capacity_completion (a b K h : ℝ) (hK : K ≠ 0) (hh : h ≠ 0)
    (hKh : K + h ≠ 0) :
    b ^ 2 / (K + h) - (b - a) ^ 2 / h =
      a ^ 2 / K - (K * b - (K + h) * a) ^ 2 / (K * h * (K + h)) := by
  field_simp
  ring

def innovationMap : H →ₗ[ℝ] H := LinearMap.id - U.starProjection.toLinearMap

/-- The screened added span is exactly the enlarged space orthogonal to the old one. -/
theorem innovation_span {ι : Type*} (v : ι → H) :
    Submodule.span ℝ (Set.range (fun j => innovation U (v j))) =
      (U ⊔ Submodule.span ℝ (Set.range v)) ⊓ Uᗮ := by
  let S := Submodule.span ℝ (Set.range (fun j => innovation U (v j)))
  have hs : S ≤ (U ⊔ Submodule.span ℝ (Set.range v)) ⊓ Uᗮ := by
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    refine ⟨?_, Submodule.sub_starProjection_mem_orthogonal _⟩
    exact (U ⊔ Submodule.span ℝ (Set.range v)).sub_mem
      ((show Submodule.span ℝ (Set.range v) ≤
        U ⊔ Submodule.span ℝ (Set.range v) from le_sup_right)
        (Submodule.subset_span ⟨j, rfl⟩))
      ((show U ≤ U ⊔ Submodule.span ℝ (Set.range v) from le_sup_left)
        (U.starProjection_apply_mem _))
  apply le_antisymm hs
  intro x hx
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp hx.1
  have hqz : innovationMap U z ∈ S := by
    clear huz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero => rw [map_zero]; exact S.zero_mem
    | add a b ha hb iha ihb => rw [map_add]; exact S.add_mem iha ihb
    | smul a y hy ih => rw [map_smul]; exact S.smul_mem a ih
  have hqu : innovationMap U u = 0 := by
    change u - U.starProjection u = 0
    rw [Submodule.starProjection_eq_self_iff.mpr hu, sub_self]
  have hqx : innovationMap U x = x := by
    change x - U.starProjection x = x
    rw [(Submodule.starProjection_apply_eq_zero_iff U).mpr hx.2, sub_zero]
  have he := congrArg (innovationMap U) huz
  rw [map_add, hqu, zero_add, hqx] at he
  rw [he] at hqz
  exact hqz


end
end RiemannResearch.Analysis.OrthogonalObservationInnovation
