/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.EvenGapPrimeReduction

/-! # Singular-series comparison with complete signed corrections

The model sigma is an arbitrary real sequence that vanishes on odd gaps.
No singular-series evaluation or Hardy--Littlewood prime-pair assertion is
assumed by the exact identities. An external singular-series estimate can
be used separately from the actual even-pair error.

Source: Montgomery--Soundararajan, Primes in short intervals,
https://arxiv.org/abs/math/0409258, equation (16), for the model target;
Matomaki--Radziwill--Tao, Correlations of the von Mangoldt and higher
divisor functions I, https://arxiv.org/abs/1707.01315, Theorem 1.3, for
comparison with averaged absolute error. These analytic theorems are
not imported as axioms or claimed to be formalized here.
-/

noncomputable section
open scoped BigOperators
open Finset
namespace RiemannResearch.Analysis.EvenGapSingularModel
open ShortIntervalVariance ShortIntervalBoundary EvenGapPrimeReduction

def modelTriangle (σ : ℕ → ℝ) (H : ℕ) : ℝ :=
  2 * ∑ h ∈ range H, triangleWeight H h * (σ (h + 1) - 1)

def evenRawDefect (σ : ℕ → ℝ) (N H : ℕ) : ℝ :=
  2 * ∑ h ∈ range H, if (h + 1) % 2 = 1 then 0 else
    triangleWeight H h * (rawGapCorrelation N (h + 1) - N * σ (h + 1))

def evenPrefixDefect (σ : ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∑ h ∈ range k, if (h + 1) % 2 = 1 then 0 else
    rawGapCorrelation N (h + 1) - N * σ (h + 1)

def meanDrift (N H : ℕ) : ℝ :=
  2 * ∑ h ∈ range H, triangleWeight H h *
    (2 * (mangoldtMass N - N) + mangoldtMassBoundary N (h + 1))

theorem evenRawDefect_prefix_exact (σ : ℕ → ℝ) (N H : ℕ) :
    evenRawDefect σ N H = 2 * ∑ k ∈ range H, evenPrefixDefect σ N k := by
  have ht := triangle_prefix
    (fun h => if h % 2 = 1 then 0 else rawGapCorrelation N h - N * σ h) H
  simp only [sum_const, card_range, nsmul_eq_mul] at ht
  unfold evenRawDefect evenPrefixDefect
  congr 1
  rw [← ht]
  apply sum_congr rfl
  intro h hh
  split_ifs <;> simp [triangleWeight]

/-- Complete model comparison: no mean, endpoint, or signed even error is lost. -/
theorem model_comparison_exact (σ : ℕ → ℝ)
    (hσ : ∀ h, h % 2 = 1 → σ h = 0) (N H : ℕ) :
    centeredOffDiagonal N H + (H : ℝ) * N * Real.log H =
      evenRawDefect σ N H + (N : ℝ) * (modelTriangle σ H + H * Real.log H) -
      meanDrift N H + boundaryCorrection centeredMangoldt N H + oddRaw N H := by
  have ht : triangularCorrelation centeredMangoldt N H =
      evenRawDefect σ N H + (N : ℝ) * modelTriangle σ H - meanDrift N H + oddRaw N H := by
    unfold triangularCorrelation evenRawDefect modelTriangle meanDrift oddRaw
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro h hh
    rw [centered_gap_raw_exact]
    by_cases ho : (h + 1) % 2 = 1
    · simp only [if_pos ho, hσ _ ho, triangleWeight]
      ring
    · simp only [if_neg ho, triangleWeight]
      ring
  rw [centeredOffDiagonal_boundary_exact, ht]
  ring

/-- Coarse absolute-error transfer; the factor H is explicit. -/
theorem evenRawDefect_abs_le (σ : ℕ → ℝ) (N H : ℕ) :
    |evenRawDefect σ N H| ≤ 2 * (H : ℝ) *
      (∑ h ∈ range H, if (h + 1) % 2 = 1 then 0 else
        |rawGapCorrelation N (h + 1) - N * σ (h + 1)|) := by
  unfold evenRawDefect
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ∑ h ∈ range H, |if (h + 1) % 2 = 1 then 0 else
        triangleWeight H h * (rawGapCorrelation N (h + 1) - N * σ (h + 1))| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2 * ∑ h ∈ range H, (H : ℝ) *
        (if (h + 1) % 2 = 1 then 0 else
          |rawGapCorrelation N (h + 1) - N * σ (h + 1)|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro h hh
      by_cases ho : (h + 1) % 2 = 1
      · simp [ho]
      · simp only [if_neg ho, abs_mul]
        have hw : |triangleWeight H h| ≤ (H : ℝ) := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
          unfold triangleWeight
          exact_mod_cast Nat.sub_le H (h + 1)
        exact mul_le_mul_of_nonneg_right hw (abs_nonneg _)
    _ = _ := by rw [← mul_sum]; ring

end RiemannResearch.Analysis.EvenGapSingularModel
