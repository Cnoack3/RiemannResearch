/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FrequencySensitiveGramBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Zero-diagonal improvements for finite Gram errors

Source: user-provided signed quadratic correction and independently developed
finite-sum refinements. The exact off-diagonal mass is retained before any
cardinality estimate. The entrywise error provider and asymptotic budget are
explicit hypotheses; these lemmas do not prove a zero-density estimate.
The actual zeta-zero consumer is ActualDirichletPolynomialOffDiagonal.
-/

open scoped BigOperators Topology
open Filter
namespace RiemannResearch.Fourier
variable {ι : Type*}

theorem offDiagonalMass_eq [DecidableEq ι] (s : Finset ι) (b : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, if i = j then (0 : ℝ) else b i * b j) =
      (∑ i ∈ s, b i) ^ 2 - ∑ i ∈ s, b i ^ 2 := by
  classical
  have hi (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, if i = j then (0 : ℝ) else b i * b j) =
        b i * (∑ j ∈ s, b j) - b i ^ 2 := by
    calc
      _ = (∑ j ∈ s, b i * b j) -
          (∑ j ∈ s, if i = j then b i * b j else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i = j <;> simp [hij]
      _ = _ := by simp [← Finset.mul_sum, hi, pow_two]
  calc
    _ = ∑ i ∈ s, (b i * (∑ j ∈ s, b j) - b i ^ 2) :=
      Finset.sum_congr rfl hi
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul]; ring

theorem finiteGramErrorPairing_norm_le_offDiagonal_frequencySpread
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (u : ι → ℝ) (η κ : ℝ)
    (hdiag : ∀ i ∈ s, R i i = 0)
    (hR : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ‖R i j‖ ≤ η + κ * (u i - u j) ^ 2) :
    ‖finiteGramErrorPairing s a R‖ ≤
      η * ((∑ i ∈ s, ‖a i‖) ^ 2 - ∑ i ∈ s, ‖a i‖^2) +
        κ * weightedFrequencySpread s (fun i => ‖a i‖) u := by
  classical
  have hn : ‖finiteGramErrorPairing s a R‖ ≤
      ∑ i ∈ s, ∑ j ∈ s,
        (η * (if i = j then 0 else ‖a i‖ * ‖a j‖) +
          κ * (‖a i‖ * ‖a j‖ * (u i - u j) ^ 2)) := by
    unfold finiteGramErrorPairing
    calc
      _ ≤ ∑ i ∈ s, ‖∑ j ∈ s, star (a i) * R i j * a j‖ := norm_sum_le s _
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖star (a i) * R i j * a j‖ :=
        Finset.sum_le_sum (fun i hi => norm_sum_le s _)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i = j
        · subst j
          simp [hdiag i hi]
        · rw [if_neg hij]
          simp only [norm_mul, norm_star]
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hR i hi j hj hij) (norm_nonneg (a i)))
            (norm_nonneg (a j))
          convert h using 1; ring
  calc
    _ ≤ _ := hn
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [offDiagonalMass_eq]
      rfl


theorem finiteGramErrorPairing_norm_le_offDiagonal_mass
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (η : ℝ)
    (hdiag : ∀ i ∈ s, R i i = 0)
    (hR : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖R i j‖ ≤ η) :
    ‖finiteGramErrorPairing s a R‖ ≤
      η * ((∑ i ∈ s, ‖a i‖) ^ 2 - ∑ i ∈ s, ‖a i‖ ^ 2) := by
  simpa using finiteGramErrorPairing_norm_le_offDiagonal_frequencySpread
    s a R (fun _ => 0) η 0 hdiag (by simpa using hR)

theorem finiteGramErrorPairing_norm_le_card_sub_one
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (η : ℝ)
    (hη : 0 ≤ η) (hdiag : ∀ i ∈ s, R i i = 0)
    (hR : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖R i j‖ ≤ η) :
    ‖finiteGramErrorPairing s a R‖ ≤
      η * ((s.card : ℝ) - 1) * (∑ i ∈ s, ‖a i‖ ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => ‖a i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    _ ≤ η * ((∑ i ∈ s, ‖a i‖) ^ 2 - ∑ i ∈ s, ‖a i‖ ^ 2) :=
      finiteGramErrorPairing_norm_le_offDiagonal_mass s a R η hdiag hR
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcs hη]

theorem growingGram_offDiagonal_remainder_tendsto_zero
    (s : ℕ → Finset ι) (a : ℕ → ι → ℂ)
    (R : ℕ → ι → ι → ℂ) (u : ℕ → ι → ℝ) (η κ : ℕ → ℝ)
    (hdiag : ∀ n, ∀ i ∈ s n, R n i i = 0)
    (hR : ∀ n, ∀ i ∈ s n, ∀ j ∈ s n, i ≠ j →
      ‖R n i j‖ ≤ η n + κ n * (u n i - u n j) ^ 2)
    (hbudget : Tendsto (fun n =>
      η n * ((∑ i ∈ s n, ‖a n i‖) ^ 2 - ∑ i ∈ s n, ‖a n i‖ ^ 2) +
      κ n * weightedFrequencySpread (s n) (fun i => ‖a n i‖) (u n))
      atTop (𝓝 0)) :
    Tendsto (fun n => finiteGramErrorPairing (s n) (a n) (R n))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => finiteGramErrorPairing_norm_le_offDiagonal_frequencySpread
      (s n) (a n) (R n) (u n) (η n) (κ n) (hdiag n) (hR n)) hbudget

end RiemannResearch.Fourier
