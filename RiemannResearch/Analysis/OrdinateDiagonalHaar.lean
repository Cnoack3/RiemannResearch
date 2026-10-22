/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ContinuousPairCoalescence
import RiemannResearch.Analysis.OrdinateLagPhase
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# The full continuous diagonal Haar law for chronological phase pairs

Source: the elementary compact-pair coalescence argument and the existing
scalar Fourier-to-Haar theorem. Scalar cancellation and height/count control
remain explicit premises. No zeta-specific analytic estimate is asserted.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.OrdinateDiagonalHaar
open ZeroOrdinate ContinuousPairCoalescence

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem circle_sample_dist_le (α a b : ℝ) :
    dist ((α*a : ℝ) : AddCircle (1 : ℝ))
      ((α*b : ℝ) : AddCircle (1 : ℝ)) ≤ |α| * |a - b| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  calc
    _ ≤ ‖α*a-α*b‖ := QuotientAddGroup.norm_mk_le_norm
    _ = _ := by rw [← mul_sub, Real.norm_eq_abs, abs_mul]

theorem circle_mean_distance_le (γ : ℕ → ℝ) (hγ : Monotone γ)
    (α : ℝ) (n ℓ : ℕ) :
    realMean n (fun j =>
      dist ((α*γ (j+ℓ) : ℝ) : AddCircle (1 : ℝ))
        ((α*γ j : ℝ) : AddCircle (1 : ℝ))) ≤
      |α| * ((ℓ : ℝ)*(γ (n+1+ℓ)-γ 0)/((n+1 : ℕ) : ℝ)) := by
  have hsum :
      (∑ j ∈ Finset.range (n+1),
        dist ((α*γ (j+ℓ) : ℝ) : AddCircle (1 : ℝ))
          ((α*γ j : ℝ) : AddCircle (1 : ℝ))) ≤
      |α| * ((ℓ : ℝ)*(γ (n+1+ℓ)-γ 0)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), |α| * (γ (j+ℓ)-γ j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hg : 0 ≤ γ (j+ℓ)-γ j :=
          sub_nonneg.mpr (hγ (Nat.le_add_right j ℓ))
        simpa only [abs_of_nonneg hg] using
          circle_sample_dist_le α (γ (j+ℓ)) (γ j)
      _ = |α| * (∑ j ∈ Finset.range (n+1), (γ (j+ℓ)-γ j)) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (OrdinateLagPhase.lag_gap_sum_le γ hγ (n+1) ℓ) (abs_nonneg α)
  unfold realMean
  calc
    _ ≤ (((n+1 : ℕ) : ℝ)⁻¹)*
        (|α| * ((ℓ : ℝ)*(γ (n+1+ℓ)-γ 0))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- All continuous pair tests converge to diagonal Haar, including at a
moving lag. This is stronger than a statement only about individual modes. -/
theorem continuous_pair_diagonal_haar
    (γ : ℕ → ℝ) (hγ : Monotone γ)
    (hcancel : FourierCancellation γ) (α : ℝ) (hα : α ≠ 0)
    (lag : ℕ → ℕ)
    (hendpoint : Tendsto
      (fun n => (lag n : ℝ)*(γ (n+1+lag n)-γ 0)/((n+1 : ℕ) : ℝ))
      atTop (𝓝 0))
    (F : C(AddCircle (1 : ℝ) × AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun n => mean n (fun j =>
      F (((α*γ j : ℝ) : AddCircle (1 : ℝ)),
        ((α*γ (j+lag n) : ℝ) : AddCircle (1 : ℝ)))))
      atTop (𝓝 (∫ x, F (x,x) ∂(AddCircle.haarAddCircle (T := 1)))) := by
  let x : ℕ → AddCircle (1 : ℝ) := fun j => ((α*γ j : ℝ) : AddCircle (1 : ℝ))
  let y : ℕ → ℕ → AddCircle (1 : ℝ) := fun n j => x (j+lag n)
  have hdisplacement : Tendsto
      (fun n => realMean n (fun j => dist (y n j) (x j)))
      atTop (𝓝 0) := by
    have hu : Tendsto
        (fun n => |α| * ((lag n : ℝ)*(γ (n+1+lag n)-γ 0)/((n+1 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hendpoint.const_mul |α|
    exact squeeze_zero
      (fun n => realMean_nonneg _ _ (fun j => dist_nonneg))
      (fun n => circle_mean_distance_le γ hγ α n (lag n)) hu
  let G : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun z => F (z,z), F.continuous.comp (continuous_id.prodMk continuous_id)⟩
  have hdiag := circle_equidistributed_of_fourier γ hcancel α hα G
  exact continuous_pair_tendsto_of_diagonal x y F _ hdisplacement hdiag

end RiemannResearch.Analysis.OrdinateDiagonalHaar
