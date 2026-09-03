/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weighted Pythagoras

Adapted from the user-provided archive `combined_audited_lean_sources.zip`,
which describes these declarations as extracted from
`combined_audited_manuscript(4).pdf`. The manuscript itself was not bundled
with this continuation, so this module records archive provenance rather than
claiming page-level source verification.
-/

open scoped BigOperators

namespace RiemannResearch.RH.CombinedAudited

variable {ι : Type*}

/-- Finite weighted Pythagoras. -/
theorem weighted_pythagorean (s : Finset ι) (w x y : ι → ℝ)
    (hxy : ∑ i ∈ s, w i * x i * y i = 0) :
    (∑ i ∈ s, w i * (x i + y i) ^ 2) =
      (∑ i ∈ s, w i * (x i) ^ 2) +
      (∑ i ∈ s, w i * (y i) ^ 2) := by
  calc
    (∑ i ∈ s, w i * (x i + y i) ^ 2) =
        ∑ i ∈ s,
          (w i * (x i) ^ 2 + w i * (y i) ^ 2 +
            2 * (w i * x i * y i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ s, w i * (x i) ^ 2) +
        (∑ i ∈ s, w i * (y i) ^ 2) +
        2 * (∑ i ∈ s, w i * x i * y i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (∑ i ∈ s, w i * (x i) ^ 2) +
        (∑ i ∈ s, w i * (y i) ^ 2) := by
      rw [hxy]
      ring

/-- A finite law-of-total-variance identity under exact orthogonality. -/
theorem finite_total_variance (s : Finset ι) (w x m : ι → ℝ)
    (hcross : ∑ i ∈ s, w i * (x i - m i) * m i = 0) :
    (∑ i ∈ s, w i * (x i) ^ 2) =
      (∑ i ∈ s, w i * (x i - m i) ^ 2) +
      (∑ i ∈ s, w i * (m i) ^ 2) := by
  have h := weighted_pythagorean s w (fun i => x i - m i) m hcross
  simpa only [sub_add_cancel] using h

/-- Centering at the actual weighted mean proves the cross-term cancellation,
rather than assuming it. -/
theorem weighted_centered_cross (s : Finset ι) (w x : ι → ℝ)
    (hW : (∑ i ∈ s, w i) ≠ 0) :
    let μ := (∑ i ∈ s, w i * x i) / (∑ i ∈ s, w i)
    ∑ i ∈ s, w i * (x i - μ) * μ = 0 := by
  dsimp only
  let μ : ℝ := (∑ i ∈ s, w i * x i) / (∑ i ∈ s, w i)
  have hcenter : (∑ i ∈ s, w i * (x i - μ)) = 0 := by
    calc
      (∑ i ∈ s, w i * (x i - μ)) =
          ∑ i ∈ s, (w i * x i - w i * μ) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ s, w i * x i) - (∑ i ∈ s, w i) * μ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = 0 := by
        dsimp [μ]
        field_simp [hW]
        ring
  rw [← Finset.sum_mul, hcenter, zero_mul]

/-- Total variance at the weighted mean, with orthogonality discharged
algebraically from the nonzero total-weight hypothesis. -/
theorem finite_total_variance_at_weighted_mean
    (s : Finset ι) (w x : ι → ℝ) (hW : (∑ i ∈ s, w i) ≠ 0) :
    let μ := (∑ i ∈ s, w i * x i) / (∑ i ∈ s, w i)
    (∑ i ∈ s, w i * (x i) ^ 2) =
      (∑ i ∈ s, w i * (x i - μ) ^ 2) +
      (∑ i ∈ s, w i * μ ^ 2) := by
  dsimp only
  let μ : ℝ := (∑ i ∈ s, w i * x i) / (∑ i ∈ s, w i)
  have hcross : (∑ i ∈ s, w i * (x i - μ) * μ) = 0 := by
    simpa [μ] using weighted_centered_cross s w x hW
  have h := weighted_pythagorean s w (fun i => x i - μ) (fun _ => μ) hcross
  simpa only [sub_add_cancel] using h

end RiemannResearch.RH.CombinedAudited
