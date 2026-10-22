/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.PrimeGapCurvature

/-!
# Finite compression of triple determinants through curvature

This module packages arbitrary finite families of ordered triple determinants
as linear functionals of adjacent curvature, then records the induced
nonnegative weighted energy.  It is an auxiliary finite-dimensional result:
it neither identifies this energy with a Weil form nor proves RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

open scoped BigOperators

noncomputable section

/-- The explicit adjacent-curvature functional associated to the ordered
triple `i < j < k`. -/
def tripleCurvatureLinearMap
    (t : ℕ → ℝ) (i j k : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun c :=
    (t k - t j) *
        (∑ r ∈ Finset.range (j - i),
          (t (i + r + 1) - t i) * c (i + r)) +
      (t j - t i) *
        (∑ r ∈ Finset.range (k - j - 1),
          (t k - t (j + r + 1)) * c (j + r))
  map_add' c d := by
    simp [mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a c := by
    change
      (t k - t j) *
          (∑ r ∈ Finset.range (j - i),
            (t (i + r + 1) - t i) * (a * c (i + r))) +
        (t j - t i) *
          (∑ r ∈ Finset.range (k - j - 1),
            (t k - t (j + r + 1)) * (a * c (j + r))) =
        a *
          ((t k - t j) *
              (∑ r ∈ Finset.range (j - i),
                (t (i + r + 1) - t i) * c (i + r)) +
            (t j - t i) *
              (∑ r ∈ Finset.range (k - j - 1),
                (t k - t (j + r + 1)) * c (j + r)))
    have hL :
        (∑ r ∈ Finset.range (j - i),
          (t (i + r + 1) - t i) * (a * c (i + r))) =
          a * ∑ r ∈ Finset.range (j - i),
            (t (i + r + 1) - t i) * c (i + r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    have hR :
        (∑ r ∈ Finset.range (k - j - 1),
          (t k - t (j + r + 1)) * (a * c (j + r))) =
          a * ∑ r ∈ Finset.range (k - j - 1),
            (t k - t (j + r + 1)) * c (j + r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hL, hR]
    ring

/-- The vector of curvature functionals for an indexed family of triples. -/
def selectedTripleCurvatureMap
    {ι : Type*} (t : ℕ → ℝ) (i j k : ι → ℕ) :
    (ℕ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun c x := tripleCurvatureLinearMap t (i x) (j x) (k x) c
  map_add' c d := by
    ext x
    exact (tripleCurvatureLinearMap t (i x) (j x) (k x)).map_add c d
  map_smul' a c := by
    ext x
    exact (tripleCurvatureLinearMap t (i x) (j x) (k x)).map_smul a c

/-- A finite diagonal weighted energy of the selected curvature map. -/
def selectedTripleCurvatureEnergy
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (t : ℕ → ℝ) (i j k : ι → ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ x ∈ s, w x * (selectedTripleCurvatureMap t i j k c x) ^ 2

theorem selectedTripleCurvatureMap_apply_adjacentCurvature
    {ι : Type*} (t z : ℕ → ℝ) (i j k : ι → ℕ) (x : ι)
    (hij : i x < j x) (hjk : j x < k x)
    (hgap : ∀ q, i x ≤ q → q < k x → gap t q ≠ 0) :
    selectedTripleCurvatureMap t i j k
        (fun r ↦ adjacentCurvature t z r) x =
      tripleDet t z (i x) (j x) (k x) := by
  simpa [selectedTripleCurvatureMap, tripleCurvatureLinearMap] using
    (tripleDet_eq_weighted_adjacentCurvatures_of_lt
      t z (i x) (j x) (k x) hij hjk hgap).symm

/-- Exact all-selected-triples factorization through adjacent curvature. -/
theorem sum_weight_mul_tripleDet_sq_eq_selectedTripleCurvatureEnergy
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (t z : ℕ → ℝ) (i j k : ι → ℕ)
    (hij : ∀ x ∈ s, i x < j x)
    (hjk : ∀ x ∈ s, j x < k x)
    (hgap : ∀ x ∈ s, ∀ q, i x ≤ q → q < k x → gap t q ≠ 0) :
    (∑ x ∈ s, w x * (tripleDet t z (i x) (j x) (k x)) ^ 2) =
      selectedTripleCurvatureEnergy s w t i j k
        (fun r ↦ adjacentCurvature t z r) := by
  classical
  simp only [selectedTripleCurvatureEnergy]
  apply Finset.sum_congr rfl
  intro x hx
  rw [selectedTripleCurvatureMap_apply_adjacentCurvature
    t z i j k x (hij x hx) (hjk x hx) (hgap x hx)]

/-- Nonnegative weights make the induced finite curvature energy PSD.
This is auxiliary and makes no identification with a Weil form. -/
theorem selectedTripleCurvatureEnergy_nonneg
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (t : ℕ → ℝ) (i j k : ι → ℕ) (c : ℕ → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    0 ≤ selectedTripleCurvatureEnergy s w t i j k c := by
  exact Finset.sum_nonneg fun x hx ↦
    mul_nonneg (hw x hx) (sq_nonneg _)

end

end RiemannResearch.RH.PrimeGapCurvature
