/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite weighted-energy certificates

Finite Cauchy--Schwarz bounds that turn any explicitly chosen linear functional
into a rigorous lower bound for a weighted quadratic energy.

Source: the user-provided report
`rh_irreducible_targets_progress_2026-09-03`, especially the adjacent
prime-curvature reduction on pages 2--5. The report motivates the certificate;
the proofs below are independent finite-dimensional algebra.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra

/-- Weighted Cauchy--Schwarz after rescaling by nonzero coordinate weights. -/
theorem weighted_functional_sq_le
    {ι : Type*} (s : Finset ι) (u c x : ι → ℝ)
    (hu : ∀ i ∈ s, u i ≠ 0) :
    (∑ i ∈ s, c i * x i) ^ 2 ≤
      (∑ i ∈ s, (u i * x i) ^ 2) *
        (∑ i ∈ s, (c i / u i) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => u i * x i) (fun i => c i / u i)
  have hsum :
      (∑ i ∈ s, (u i * x i) * (c i / u i)) =
        ∑ i ∈ s, c i * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hu i hi]
  rw [hsum] at h
  exact h

/-- A single normalized functional is a lower certificate for the full
weighted energy. For prime curvature, choosing `c` to be one curvature row
gives the one-row obstruction described by the progress report. -/
theorem weighted_functional_energy_lower_bound
    {ι : Type*} (s : Finset ι) (u c x : ι → ℝ)
    (hu : ∀ i ∈ s, u i ≠ 0)
    (hdual : 0 < ∑ i ∈ s, (c i / u i) ^ 2) :
    (∑ i ∈ s, c i * x i) ^ 2 /
        (∑ i ∈ s, (c i / u i) ^ 2) ≤
      ∑ i ∈ s, (u i * x i) ^ 2 := by
  apply (div_le_iff₀ hdual).2
  simpa [mul_comm] using weighted_functional_sq_le s u c x hu


/-- Double-sum identity for the determinant of the weighted affine normal
matrix. It makes the strict-positivity input for affine projection explicit. -/
theorem affine_normal_det_double_sum
    {ι : Type*} (s : Finset ι) (w t : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s,
        w i * w j * (t i - t j) ^ 2) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * (t i) ^ 2) -
        (∑ i ∈ s, w i * t i) ^ 2) := by
  have hA :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * (t i) ^ 2) =
        (∑ i ∈ s, w i * (t i) ^ 2) * (∑ j ∈ s, w j) := by
    calc
      _ = ∑ i ∈ s, (w i * (t i) ^ 2) * (∑ j ∈ s, w j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.sum_mul]
  have hB :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * t i * t j) =
        (∑ i ∈ s, w i * t i) * (∑ j ∈ s, w j * t j) := by
    calc
      _ = ∑ i ∈ s, (w i * t i) * (∑ j ∈ s, w j * t j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.sum_mul]
  have hC :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * (t j) ^ 2) =
        (∑ i ∈ s, w i) * (∑ j ∈ s, w j * (t j) ^ 2) := by
    calc
      _ = ∑ i ∈ s, w i * (∑ j ∈ s, w j * (t j) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.sum_mul]
  calc
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (t i - t j) ^ 2) =
        (∑ i ∈ s, ∑ j ∈ s,
          (w i * w j * (t i) ^ 2 -
            2 * (w i * w j * t i * t j) +
            w i * w j * (t j) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ i ∈ s, ∑ j ∈ s, w i * w j * (t i) ^ 2) -
          2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * t i * t j) +
          (∑ i ∈ s, ∑ j ∈ s, w i * w j * (t j) ^ 2) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = _ := by rw [hA, hB, hC]; ring

/-- Nonnegative coordinate weights make the affine normal determinant
nonnegative. -/
theorem affine_normal_det_nonnegative
    {ι : Type*} (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (t i) ^ 2) -
      (∑ i ∈ s, w i * t i) ^ 2 := by
  have hsum : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      w i * w j * (t i - t j) ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)
  rw [affine_normal_det_double_sum s w t] at hsum
  linarith

/-- The affine normal determinant is strictly positive once two distinct
locations carry positive weight. -/
theorem affine_normal_det_positive
    {ι : Type*} (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hpair : ∃ i ∈ s, ∃ j ∈ s,
      0 < w i ∧ 0 < w j ∧ t i ≠ t j) :
    0 < (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (t i) ^ 2) -
      (∑ i ∈ s, w i * t i) ^ 2 := by
  rcases hpair with ⟨i, hi, j, hj, hwi, hwj, ht⟩
  have hterm : 0 < w i * w j * (t i - t j) ^ 2 :=
    mul_pos (mul_pos hwi hwj) (sq_pos_of_ne_zero (sub_ne_zero.mpr ht))
  have hsum : 0 < ∑ i ∈ s, ∑ j ∈ s,
      w i * w j * (t i - t j) ^ 2 := by
    apply Finset.sum_pos'
    · intro k hk
      apply Finset.sum_nonneg
      intro l hl
      exact mul_nonneg (mul_nonneg (hw k hk) (hw l hl)) (sq_nonneg _)
    · refine ⟨i, hi, ?_⟩
      apply Finset.sum_pos'
      · intro l hl
        exact mul_nonneg (mul_nonneg (hw i hi) (hw l hl)) (sq_nonneg _)
      · exact ⟨j, hj, hterm⟩
  rw [affine_normal_det_double_sum s w t] at hsum
  linarith

/-- Exact square completion with reciprocal coordinate weights.
Source: user-provided RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md,
§§6 and 12. Used by genuine Möbius witness error-floor certificates. -/
theorem finite_weighted_square_completion {ι : Type*} (s : Finset ι)
    (w c x : ι → ℝ) (t : ℝ) (hw : ∀ i ∈ s, w i ≠ 0) :
    (∑ i ∈ s, (x i - t*w i*c i)^2 / w i) =
      (∑ i ∈ s, (x i)^2 / w i) - 2*t*(∑ i ∈ s, c i*x i) +
        t^2*(∑ i ∈ s, w i*(c i)^2) := by
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hw i hi]
  ring

/-- A finite dual bound; positive weights and positive dual energy are explicit. -/
theorem finite_weighted_dual_bound {ι : Type*} (s : Finset ι)
    (w c x : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hn : 0 < ∑ i ∈ s, w i*(c i)^2) :
    (∑ i ∈ s, c i*x i)^2 / (∑ i ∈ s, w i*(c i)^2) ≤
      ∑ i ∈ s, (x i)^2 / w i := by
  let L := ∑ i ∈ s, c i*x i
  let N := ∑ i ∈ s, w i*(c i)^2
  have h := finite_weighted_square_completion s w c x (L/N)
    (fun i hi => ne_of_gt (hw i hi))
  have hnonneg : 0 ≤ ∑ i ∈ s, (x i - (L/N)*w i*c i)^2 / w i := by
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (sq_nonneg _) (le_of_lt (hw i hi))
  have hn0 : N ≠ 0 := ne_of_gt hn
  change L^2/N ≤ _
  have he : -(2*(L/N)*L)+(L/N)^2*N = -(L^2/N) := by field_simp; ring
  change _ = _ - 2*(L/N)*L+(L/N)^2*N at h
  rw [sub_eq_add_neg, add_assoc, he] at h
  linarith

end RiemannResearch.LinearAlgebra
