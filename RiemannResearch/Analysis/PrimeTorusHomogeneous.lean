/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusPlancherel
import RiemannResearch.Analysis.PrimeTorusFourierProducts
import RiemannResearch.Analysis.PrimeTorusHaarSpecialization
import RiemannResearch.Analysis.PoissonHaarSpecialization
import Mathlib.Tactic.Push

/-! # Homogeneous Haar Parseval with the signed prime-torus density

Source: user-provided Montgomery handoff, Section 3, and the existing Fourier
coefficient formula in PrimeTorusHaarSpecialization. A zero-total-degree
frequency has zero axis multiplier. Consequently every finite homogeneous
Fourier polynomial has exactly its Haar energy against the signed weight
1 + density. This weight is not asserted to be a positive probability density
or the empirical law of raw zeros. Actual-zero comparison errors are separate.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.PrimeTorusHaar
open RiemannResearch.Analysis.PoissonHaar
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem axisMultiplier_eq_zero_of_sum_eq_zero (c a : ι → ℝ) (k : ι → ℤ)
    (hk : ∑ i, k i = 0) : axisMultiplier c a k = 0 := by
  unfold axisMultiplier
  apply Finset.sum_eq_zero
  intro i hi
  suffices hz : (∏ j : ι, if j = i then centeredPoissonMultiplier (a i) (k j)
      else if k j = 0 then (1 : ℂ) else 0) = 0 by rw [hz, mul_zero]
  by_cases h : ∀ j, j ≠ i → k j = 0
  · have hs : ∑ j, k j = k i := by
      apply Finset.sum_eq_single i
      · intro j hj hji; exact h j hji
      · simp
    have hki : k i = 0 := hs.symm.trans hk
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hki, centeredPoissonMultiplier])
  · push Not at h
    obtain ⟨j, hji, hkj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hji, hkj])

theorem haarIntegral_character_mul_star_density_of_degree
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1)
    (k l : ι → ℤ) (hdeg : ∑ i, k i = ∑ i, l i) :
    haarIntegral (character k * star (character l) * density c a) = 0 := by
  rw [character_mul_star, haarIntegral_character_density c a ha ha1]
  apply axisMultiplier_eq_zero_of_sum_eq_zero
  simpa only [Pi.sub_apply, Finset.sum_sub_distrib, sub_eq_zero] using hdeg

theorem haarIntegral_homogeneous_density_zero
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1)
    (s : Finset (ι → ℤ)) (b : (ι → ℤ) → ℂ) (d : ℤ)
    (hd : ∀ k ∈ s, ∑ i, k i = d) :
    haarIntegral ((∑ k ∈ s, b k • character k) *
      star (∑ k ∈ s, b k • character k) * density c a) = 0 := by
  simp only [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  rw [haarIntegral_character_mul_star_density_of_degree c a ha ha1 l k
    ((hd l hl).trans (hd k hk).symm)]
  simp

theorem haarIntegral_homogeneous_parseval
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1)
    (s : Finset (ι → ℤ)) (b : (ι → ℤ) → ℂ) (d : ℤ)
    (hd : ∀ k ∈ s, ∑ i, k i = d) :
    let P := ∑ k ∈ s, b k • character k
    haarIntegral (P * star P * (1 + density c a)) =
      ((∑' k : ι → ℤ, ‖FiniteTorusWiener.coeff P k‖ ^ 2 : ℝ) : ℂ) := by
  dsimp only
  rw [mul_add, mul_one, map_add, haarIntegral_homogeneous_density_zero c a ha ha1 s b d hd,
    add_zero, haarIntegral_mul_star_self]
end RiemannResearch.Analysis.PrimeTorusHaar
