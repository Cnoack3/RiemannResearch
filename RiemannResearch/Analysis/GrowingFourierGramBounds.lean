/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Fourier Gram error bounds

Source: user-provided manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`,
Theorem `growing-phase-gram` (entrywise-error part of the proof).

The uniform rational-character estimate, the weighted Schur estimate for
the von Mangoldt covariance matrix, and all zeta-zero providers are explicit
external analytic obligations. The results here prove the finite support
loss exactly, without presuming any of those providers.
-/

open scoped BigOperators

namespace RiemannResearch.Fourier

variable {ι : Type*}

/-- Exact complex Gram-error pairing over a finite dictionary. -/
def finiteGramErrorPairing (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s, star (a i) * R i j * a j

/-- The entrywise error has a sharp elementary Wiener-square loss. -/
theorem finiteGramErrorPairing_norm_le_wiener_sq
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (η : ℝ)
    (hR : ∀ i ∈ s, ∀ j ∈ s, ‖R i j‖ ≤ η) :
    ‖finiteGramErrorPairing s a R‖ ≤ η * (∑ i ∈ s, ‖a i‖) ^ 2 := by
  unfold finiteGramErrorPairing
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ s, star (a i) * R i j * a j‖ := norm_sum_le s _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖star (a i) * R i j * a j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le s _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * η * ‖a j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hR i hi j hj) (norm_nonneg _)) (norm_nonneg _)
    _ = η * (∑ i ∈ s, ‖a i‖) ^ 2 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Consequently the support loss is exactly cardinality in the squared
    Euclidean coefficient norm. No spectral or zeta-specific assumptions enter. -/
theorem finiteGramErrorPairing_norm_le_card_l2
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (η : ℝ)
    (hη : 0 ≤ η) (hR : ∀ i ∈ s, ∀ j ∈ s, ‖R i j‖ ≤ η) :
    ‖finiteGramErrorPairing s a R‖ ≤
      η * (s.card : ℝ) * (∑ i ∈ s, ‖a i‖ ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    _ ≤ η * (∑ i ∈ s, ‖a i‖) ^ 2 :=
      finiteGramErrorPairing_norm_le_wiener_sq s a R η hR
    _ ≤ η * ((∑ i ∈ s, ‖a i‖ ^ 2) * (s.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcs hη
    _ = _ := by ring

/-- Complete signed subtraction before any norm estimate. -/
theorem finiteGramErrorPairing_sub
    (s : Finset ι) (a : ι → ℂ) (R S : ι → ι → ℂ) :
    finiteGramErrorPairing s a (fun i j => R i j - S i j) =
      finiteGramErrorPairing s a R - finiteGramErrorPairing s a S := by
  unfold finiteGramErrorPairing
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- Unnormalized weighted frequency variance. The definition is meaningful
for arbitrary real weights; nonnegativity requires nonnegative weights. -/
def finiteFrequencyDispersion
    (s : Finset ι) (w ℓ : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (ℓ i) ^ 2) -
    (∑ i ∈ s, w i * ℓ i) ^ 2

/-- Exact pair-difference identity, retaining the negative first-moment square.

Source: `Prime_Phase_Haar_Research_Continuation_20261004.md`, Section 3,
the coefficient-sensitive covariance proof. -/
theorem weighted_pairwise_frequency_sq_eq
    (s : Finset ι) (w ℓ : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (ℓ i - ℓ j) ^ 2) =
      2 * finiteFrequencyDispersion s w ℓ := by
  classical
  unfold finiteFrequencyDispersion
  have hterm (i j : ι) :
      w i * w j * (ℓ i - ℓ j) ^ 2 =
        (w i * (ℓ i) ^ 2) * w j +
          w i * (w j * (ℓ j) ^ 2) -
          (2 * (w i * ℓ i)) * (w j * ℓ j) := by
    ring
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring_nf
  simp only [← Finset.sum_mul]
  ring

theorem finiteFrequencyDispersion_nonneg
    (s : Finset ι) (w ℓ : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ finiteFrequencyDispersion s w ℓ := by
  have h :
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (ℓ i - ℓ j) ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)
  rw [weighted_pairwise_frequency_sq_eq] at h
  linarith

/-- A common frequency translation does not alter the exact dispersion.
Thus logarithms may be centered before estimating their moments. -/
theorem finiteFrequencyDispersion_add_const
    (s : Finset ι) (w ℓ : ι → ℝ) (c : ℝ) :
    finiteFrequencyDispersion s w (fun i => ℓ i + c) =
      finiteFrequencyDispersion s w ℓ := by
  have h :
      2 * finiteFrequencyDispersion s w (fun i => ℓ i + c) =
        2 * finiteFrequencyDispersion s w ℓ := by
    rw [← weighted_pairwise_frequency_sq_eq,
      ← weighted_pairwise_frequency_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  linarith

/-- Exact aggregation of a squared-frequency-distance majorant. -/
theorem weighted_frequency_majorant_sum
    (s : Finset ι) (w ℓ : ι → ℝ) (η δ : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s,
      (w i * w j) * (η * (ℓ i - ℓ j) ^ 2 + δ)) =
        2 * η * finiteFrequencyDispersion s w ℓ +
          δ * (∑ i ∈ s, w i) ^ 2 := by
  classical
  have hterm (i j : ι) :
      (w i * w j) * (η * (ℓ i - ℓ j) ^ 2 + δ) =
        η * (w i * w j * (ℓ i - ℓ j) ^ 2) +
          δ * (w i * w j) := by
    ring
  calc
    _ = η * (∑ i ∈ s, ∑ j ∈ s,
          w i * w j * (ℓ i - ℓ j) ^ 2) +
        δ * (∑ i ∈ s, w i) ^ 2 := by
      simp_rw [hterm, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ = _ := by
      rw [weighted_pairwise_frequency_sq_eq]
      ring

/-- Coefficient-sensitive Gram remainder bound. A common frequency
translation costs nothing. The `W₀ W₂ - W₁²` cancellation is retained.

For rational prime-phase sampling, use `ℓ q = log q`; the analytic
modewise remainder remains an explicit hypothesis. No zeta-density or
Landau provider is asserted here. -/
theorem finiteGramErrorPairing_norm_le_frequency_dispersion
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ)
    (ℓ : ι → ℝ) (η δ : ℝ)
    (hR : ∀ i ∈ s, ∀ j ∈ s,
      ‖R i j‖ ≤ η * (ℓ i - ℓ j) ^ 2 + δ) :
    ‖finiteGramErrorPairing s a R‖ ≤
      2 * η * finiteFrequencyDispersion s (fun i => ‖a i‖) ℓ +
        δ * (∑ i ∈ s, ‖a i‖) ^ 2 := by
  unfold finiteGramErrorPairing
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ s, star (a i) * R i j * a j‖ :=
      norm_sum_le s _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ‖star (a i) * R i j * a j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le s _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        (‖a i‖ * ‖a j‖) *
          (η * (ℓ i - ℓ j) ^ 2 + δ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul, norm_star]
      calc
        _ ≤ ‖a i‖ * (η * (ℓ i - ℓ j) ^ 2 + δ) * ‖a j‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hR i hi j hj) (norm_nonneg _))
            (norm_nonneg _)
        _ = _ := by ring
    _ = _ := weighted_frequency_majorant_sum s (fun i => ‖a i‖) ℓ η δ

end RiemannResearch.Fourier
