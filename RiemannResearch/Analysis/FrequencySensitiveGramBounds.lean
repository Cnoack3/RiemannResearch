/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GrowingFourierGramBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Frequency-sensitive finite Fourier Gram bounds

Source: the user-provided unconditional zeta-zero research agenda, §7,
Priorities 1–2;
the algebraic identities and estimates below are direct finite-sum arguments.
The exact negative square is retained. Any zeta-specific entrywise remainder
estimate is an explicit hypothesis, never an axiom or a consequence of RH.
-/

open scoped BigOperators Topology
open Filter

namespace RiemannResearch.Fourier

variable {ι : Type*}

/-- Pairwise squared frequency spread. Real weights may be signed. -/
def weightedFrequencySpread (s : Finset ι) (w u : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, w i * w j * (u i - u j) ^ 2

/-- Exact frequency-spread identity, including the negative square term.
No sign assumption on the real weights is needed. -/
theorem weightedFrequencySpread_eq (s : Finset ι) (w u : ι → ℝ) :
    weightedFrequencySpread s w u =
      2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * u i ^ 2) -
        2 * (∑ i ∈ s, w i * u i) ^ 2 := by
  unfold weightedFrequencySpread
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        ((w i * u i ^ 2) * w j + w i * (w j * u j ^ 2) -
          (2 * (w i * u i)) * (w j * u j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring_nf <;> simp only [← Finset.sum_mul] <;> ring

/-- A common frequency translation changes none of the pairwise differences. -/
theorem weightedFrequencySpread_shift (s : Finset ι) (w u : ι → ℝ) (c : ℝ) :
    weightedFrequencySpread s w (fun i => u i - c) =
      weightedFrequencySpread s w u := by
  unfold weightedFrequencySpread
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The exact identity can be centered at any real frequency. -/
theorem weightedFrequencySpread_eq_centered (s : Finset ι) (w u : ι → ℝ) (c : ℝ) :
    weightedFrequencySpread s w u =
      2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (u i - c) ^ 2) -
        2 * (∑ i ∈ s, w i * (u i - c)) ^ 2 := by
  rw [← weightedFrequencySpread_shift s w u c]
  exact weightedFrequencySpread_eq s w (fun i => u i - c)

/-- Nonnegative weights give nonnegative pairwise spread. -/
theorem weightedFrequencySpread_nonneg (s : Finset ι) (w u : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ weightedFrequencySpread s w u := by
  unfold weightedFrequencySpread
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)

/-- A second-moment upper bound; the preceding equality records exactly
what this estimate discards. The weights may again be signed. -/
theorem weightedFrequencySpread_le_centered (s : Finset ι) (w u : ι → ℝ) (c : ℝ) :
    weightedFrequencySpread s w u ≤
      2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (u i - c) ^ 2) := by
  rw [weightedFrequencySpread_eq_centered s w u c]
  nlinarith [sq_nonneg (∑ i ∈ s, w i * (u i - c))]

/-- Factoring the precise quadratic entrywise error budget. -/
theorem weightedFrequencyErrorBudget_eq (s : Finset ι) (w u : ι → ℝ) (η κ : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (η + κ * (u i - u j) ^ 2)) =
      η * (∑ i ∈ s, w i) ^ 2 + κ * weightedFrequencySpread s w u := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (η * (w i * w j) + κ * (w i * w j * (u i - u j) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      simp only [weightedFrequencySpread, pow_two]

/-- Coefficient-weighted control retains each pair's own frequency gap.
In particular, it avoids replacing every gap by a maximum dictionary radius. -/
theorem finiteGramErrorPairing_norm_le_frequencySpread
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (u : ι → ℝ) (η κ : ℝ)
    (hR : ∀ i ∈ s, ∀ j ∈ s, ‖R i j‖ ≤ η + κ * (u i - u j) ^ 2) :
    ‖finiteGramErrorPairing s a R‖ ≤
      η * (∑ i ∈ s, ‖a i‖) ^ 2 +
        κ * weightedFrequencySpread s (fun i => ‖a i‖) u := by
  unfold finiteGramErrorPairing
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ s, star (a i) * R i j * a j‖ := norm_sum_le s _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖star (a i) * R i j * a j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le s _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ‖a i‖ * ‖a j‖ * (η + κ * (u i - u j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul, norm_star]
      calc
        _ ≤ ‖a i‖ * (η + κ * (u i - u j) ^ 2) * ‖a j‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hR i hi j hj) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := weightedFrequencyErrorBudget_eq s (fun i => ‖a i‖) u η κ

/-- Explicit frequency-variance remainder, with its negative square preserved. -/
theorem finiteGramErrorPairing_norm_le_frequencyVariance
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (u : ι → ℝ) (η κ : ℝ)
    (hR : ∀ i ∈ s, ∀ j ∈ s, ‖R i j‖ ≤ η + κ * (u i - u j) ^ 2) :
    ‖finiteGramErrorPairing s a R‖ ≤
      η * (∑ i ∈ s, ‖a i‖) ^ 2 +
        κ * (2 * (∑ i ∈ s, ‖a i‖) * (∑ i ∈ s, ‖a i‖ * u i ^ 2) -
          2 * (∑ i ∈ s, ‖a i‖ * u i) ^ 2) := by
  simpa only [weightedFrequencySpread_eq] using
    finiteGramErrorPairing_norm_le_frequencySpread s a R u η κ hR

/-- Exact finite Fourier Gram decomposition for a diagonal term, signed
prime contribution, and analytic remainder supplied by an external provider. -/
theorem finiteGramErrorPairing_three_term_split
    (s : Finset ι) (a : ι → ℂ) (K D B R : ι → ι → ℂ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, K i j = D i j + B i j + R i j) :
    finiteGramErrorPairing s a K = finiteGramErrorPairing s a D +
      finiteGramErrorPairing s a B + finiteGramErrorPairing s a R := by
  unfold finiteGramErrorPairing
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (star (a i) * D i j * a j + star (a i) * B i j * a j +
          star (a i) * R i j * a j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hK i hi j hj]
      ring
    _ = _ := by simp only [Finset.sum_add_distrib]

/-- A growing dictionary is permitted when its actual coefficient-weighted
frequency budget tends to zero. The diagonal and signed arithmetic terms
remain in the limit statement. No support-cardinality bound is substituted. -/
theorem growingGram_signed_remainder_tendsto_zero
    (s : ℕ → Finset ι) (a : ℕ → ι → ℂ)
    (K D B R : ℕ → ι → ι → ℂ) (u : ℕ → ι → ℝ) (η κ : ℕ → ℝ)
    (hK : ∀ n, ∀ i ∈ s n, ∀ j ∈ s n,
      K n i j = D n i j + B n i j + R n i j)
    (hR : ∀ n, ∀ i ∈ s n, ∀ j ∈ s n,
      ‖R n i j‖ ≤ η n + κ n * (u n i - u n j) ^ 2)
    (hbudget : Tendsto (fun n =>
      η n * (∑ i ∈ s n, ‖a n i‖) ^ 2 +
        κ n * weightedFrequencySpread (s n) (fun i => ‖a n i‖) (u n))
      atTop (𝓝 0)) :
    Tendsto (fun n => finiteGramErrorPairing (s n) (a n) (K n) -
      finiteGramErrorPairing (s n) (a n) (D n) -
      finiteGramErrorPairing (s n) (a n) (B n)) atTop (𝓝 0) := by
  have heq : (fun n => finiteGramErrorPairing (s n) (a n) (K n) -
      finiteGramErrorPairing (s n) (a n) (D n) -
      finiteGramErrorPairing (s n) (a n) (B n)) =
      (fun n => finiteGramErrorPairing (s n) (a n) (R n)) := by
    funext n
    rw [finiteGramErrorPairing_three_term_split
      (s n) (a n) (K n) (D n) (B n) (R n) (hK n)]
    ring
  rw [heq]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => finiteGramErrorPairing_norm_le_frequencySpread
      (s n) (a n) (R n) (u n) (η n) (κ n) (hR n)) hbudget

end RiemannResearch.Fourier
