/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.NestedProjectionEnergy
import RiemannResearch.Analysis.ProjectionTrialEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Exact errors and equality conditions for random subspace projections

Source: user-provided nested-projection question, 14 October 2026.
The deterministic identity is reused from NestedProjectionEnergy. The finite
weighted sums and Bochner integrals retain the complete nonnegative gap.
The RH consumer is QLegalAtomSelection; no density estimate is assumed here.
-/

open MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace RiemannResearch.Analysis.RandomSubspaceProjection
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (V : Submodule ℝ H) [V.HasOrthogonalProjection]
variable {ι : Type*} (W : ι → Submodule ℝ H)
  [∀ i, (W i).HasOrthogonalProjection]

theorem error_eq_iff_mem (i : ι) (hWV : W i ≤ V) (x : H) :
    ‖x - (W i).starProjection x‖ ^ 2 = ‖x - V.starProjection x‖ ^ 2 ↔
      V.starProjection x ∈ W i := by
  rw [NestedProjectionEnergy.residual_energy_eq_iff hWV]
  constructor
  · intro h
    rw [h]
    exact (W i).starProjection_apply_mem x
  · intro h
    calc
      V.starProjection x = (W i).starProjection (V.starProjection x) :=
        (Submodule.starProjection_eq_self_iff.mpr h).symm
      _ = (W i).starProjection x :=
        NestedProjectionEnergy.project_project_of_le hWV x

section Finite
variable [Fintype ι]

def expectedError (p : ι → ℝ) (x : H) : ℝ :=
  ∑ i, p i * ‖x - (W i).starProjection x‖ ^ 2

def expectedGap (p : ι → ℝ) (x : H) : ℝ :=
  ∑ i, p i * ‖V.starProjection x - (W i).starProjection x‖ ^ 2

theorem expected_error_eq (p : ι → ℝ) (hp : ∑ i, p i = 1)
    (hWV : ∀ i, W i ≤ V) (x : H) :
    expectedError W p x = ‖x - V.starProjection x‖ ^ 2 + expectedGap V W p x := by
  unfold expectedError expectedGap
  simp_rw [NestedProjectionEnergy.residual_energy_eq_add_gap (hWV _) x, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]

theorem expectedGap_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (x : H) :
    0 ≤ expectedGap V W p x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))

theorem error_le_expected (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hWV : ∀ i, W i ≤ V) (x : H) :
    ‖x - V.starProjection x‖ ^ 2 ≤ expectedError W p x := by
  rw [expected_error_eq V W p hsum hWV x]
  exact le_add_of_nonneg_right (expectedGap_nonneg V W p hp x)

theorem expected_error_eq_iff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hWV : ∀ i, W i ≤ V) (x : H) :
    expectedError W p x = ‖x - V.starProjection x‖ ^ 2 ↔
      ∀ i, 0 < p i → V.starProjection x ∈ W i := by
  rw [expected_error_eq V W p hsum hWV x, add_eq_left]
  change (∑ i, p i * ‖V.starProjection x - (W i).starProjection x‖ ^ 2) = 0 ↔ _
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hp i) (sq_nonneg _))]
  constructor
  · intro h i hi
    have hz := (mul_eq_zero.mp (h i (Finset.mem_univ i))).resolve_left (ne_of_gt hi)
    have he : V.starProjection x = (W i).starProjection x :=
      sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
    rw [he]
    exact (W i).starProjection_apply_mem x
  · intro h i _
    by_cases hi : p i = 0
    · simp [hi]
    · have hm := h i (lt_of_le_of_ne (hp i) (Ne.symm hi))
      have he := (error_eq_iff_mem V W i (hWV i) x).mpr hm
      have heq := (NestedProjectionEnergy.residual_energy_eq_iff (hWV i) x).mp he
      simp [heq]

theorem exists_error_le_expected (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (x : H) :
    ∃ i, 0 < p i ∧ ‖x - (W i).starProjection x‖ ^ 2 ≤ expectedError W p x := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hle (i : ι) :
      p i * expectedError W p x ≤ p i * ‖x - (W i).starProjection x‖ ^ 2 := by
    by_cases hi : p i = 0
    · simp [hi]
    · exact le_of_lt (mul_lt_mul_of_pos_left (h i (lt_of_le_of_ne (hp i) (Ne.symm hi)))
        (lt_of_le_of_ne (hp i) (Ne.symm hi)))
  have hex : ∃ i, 0 < p i := by
    by_contra hpos
    have hz : ∀ i, p i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt (fun hi => hpos ⟨i, hi⟩)) (hp i)
    simp [hz] at hsum
  obtain ⟨i, hi⟩ := hex
  have hlt := Finset.sum_lt_sum (fun j _ => hle j)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (h i hi) hi⟩
  rw [← Finset.sum_mul, hsum, one_mul] at hlt
  exact (lt_irrefl _ hlt)
end Finite

section Integral
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (U : Ω → Submodule ℝ H) [∀ ω, (U ω).HasOrthogonalProjection]

theorem integral_error_eq (hUV : ∀ ω, U ω ≤ V) (x : H)
    (hg : Integrable (fun ω => ‖V.starProjection x - (U ω).starProjection x‖ ^ 2) μ) :
    (∫ ω, ‖x - (U ω).starProjection x‖ ^ 2 ∂μ) =
      ‖x - V.starProjection x‖ ^ 2 +
        ∫ ω, ‖V.starProjection x - (U ω).starProjection x‖ ^ 2 ∂μ := by
  calc
    _ = ∫ ω, ‖x - V.starProjection x‖ ^ 2 +
        ‖V.starProjection x - (U ω).starProjection x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun ω => NestedProjectionEnergy.residual_energy_eq_add_gap (hUV ω) x)
    _ = _ := by rw [integral_add (integrable_const _) hg]; simp

theorem integral_error_eq_iff (hUV : ∀ ω, U ω ≤ V) (x : H)
    (hg : Integrable (fun ω => ‖V.starProjection x - (U ω).starProjection x‖ ^ 2) μ) :
    (∫ ω, ‖x - (U ω).starProjection x‖ ^ 2 ∂μ) =
      ‖x - V.starProjection x‖ ^ 2 ↔
      ∀ᵐ ω ∂μ, V.starProjection x ∈ U ω := by
  rw [integral_error_eq V μ U hUV x hg, add_eq_left,
    integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hg]
  constructor
  · intro h
    filter_upwards [h] with ω hω
    have he : V.starProjection x = (U ω).starProjection x :=
      sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hω))
    rw [he]
    exact (U ω).starProjection_apply_mem x
  · intro h
    filter_upwards [h] with ω hω
    have he := (NestedProjectionEnergy.residual_energy_eq_iff (hUV ω) x).mp
      ((error_eq_iff_mem V U ω (hUV ω) x).mpr hω)
    simp [he]
end Integral
end RiemannResearch.Analysis.RandomSubspaceProjection

namespace RiemannResearch.Analysis.RandomSubspaceProjection
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Convergence of sampled optimizers has exactly two nonnegative obligations. -/
theorem expected_error_tendsto_zero_iff
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (V : ℕ → Submodule ℝ H) [∀ n, (V n).HasOrthogonalProjection]
    (W : (n : ℕ) → ι n → Submodule ℝ H)
    [∀ n i, (W n i).HasOrthogonalProjection]
    (p : (n : ℕ) → ι n → ℝ) (hp : ∀ n i, 0 ≤ p n i)
    (hsum : ∀ n, ∑ i, p n i = 1)
    (hWV : ∀ n i, W n i ≤ V n) (x : H) :
    Tendsto (fun n => expectedError (W n) (p n) x) atTop (𝓝 0) ↔
      Tendsto (fun n => ‖x - (V n).starProjection x‖ ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => expectedGap (V n) (W n) (p n) x) atTop (𝓝 0) := by
  constructor
  · intro h
    refine ⟨squeeze_zero (fun _ => sq_nonneg _)
      (fun n => error_le_expected (V n) (W n) (p n) (hp n) (hsum n) (hWV n) x) h, ?_⟩
    apply squeeze_zero (fun n => expectedGap_nonneg (V n) (W n) (p n) (hp n) x) _ h
    intro n
    rw [expected_error_eq (V n) (W n) (p n) (hsum n) (hWV n) x]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rintro ⟨herror, hgap⟩
    have heq : (fun n => expectedError (W n) (p n) x) =
        (fun n => ‖x - (V n).starProjection x‖ ^ 2 +
          expectedGap (V n) (W n) (p n) x) :=
      funext (fun n => expected_error_eq (V n) (W n) (p n) (hsum n) (hWV n) x)
    rw [heq]
    simpa only [add_zero] using herror.add hgap

end RiemannResearch.Analysis.RandomSubspaceProjection

namespace RiemannResearch.Analysis.RandomSubspaceProjection
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem trial_gap_decomposition (U V : Submodule ℝ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hUV : U ≤ V)
    (x y : H) (hy : y ∈ U) :
    ‖V.starProjection x - y‖ ^ 2 =
      ‖V.starProjection x - U.starProjection x‖ ^ 2 +
        ‖U.starProjection x - y‖ ^ 2 := by
  simpa only [NestedProjectionEnergy.project_project_of_le hUV x] using
    projection_trial_energy U (V.starProjection x) y hy
end RiemannResearch.Analysis.RandomSubspaceProjection
