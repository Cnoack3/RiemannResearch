import RiemannResearch.Analysis.LogarithmicSamplingBounds

/-!
# Bounded logarithmic envelopes in weighted arithmetic rows

On the positive integer square `1..X`, the squared logarithmic ratio is at
most `log(X)^2`.  Multiplying this pointwise estimate by the nonnegative
arithmetic row weights transfers an existing weighted row budget without any
symmetry assumption on the arithmetic kernel.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualPrimePowerWeightedRows

open LogarithmicSamplingBounds

/-- The one-sided logarithmic ratio lies between `0` and `log X`. -/
theorem logSquareEnvelope_le_log_sq_of_le {n m X : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnX : n ≤ X) :
    logSquareEnvelope n m ≤ Real.log (X : ℝ) ^ 2 := by
  have hmR1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmR : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hmR1
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hnR : (0 : ℝ) < (n : ℝ) := hmR.trans_le hmnR
  have hnXR : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
  have hXR1 : (1 : ℝ) ≤ (X : ℝ) := hmR1.trans (hmnR.trans hnXR)
  have hratio1 : (1 : ℝ) ≤ (n : ℝ) / (m : ℝ) :=
    (le_div_iff₀ hmR).mpr (by simpa only [one_mul] using hmnR)
  have hratioX : (n : ℝ) / (m : ℝ) ≤ (X : ℝ) :=
    (div_le_self hnR.le hmR1).trans hnXR
  have hlog0 : 0 ≤ Real.log ((n : ℝ) / (m : ℝ)) := Real.log_nonneg hratio1
  have hlogX0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXR1
  have hlogX : Real.log ((n : ℝ) / (m : ℝ)) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (div_pos hnR hmR) hratioX
  exact (sq_le_sq₀ hlog0 hlogX0).mpr hlogX

/-- Every squared logarithmic ratio in the positive integer square is bounded
by `log(X)^2`.  The input bounds themselves imply `1 ≤ X`. -/
theorem logSquareEnvelope_le_log_sq {n m X : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnX : n ≤ X) (hmX : m ≤ X) :
    logSquareEnvelope n m ≤ Real.log (X : ℝ) ^ 2 := by
  rcases le_total m n with hmn | hnm
  · exact logSquareEnvelope_le_log_sq_of_le hm hmn hnX
  · calc
      logSquareEnvelope n m = logSquareEnvelope m n := logSquareEnvelope_symm n m
      _ ≤ Real.log (X : ℝ) ^ 2 := logSquareEnvelope_le_log_sq_of_le hn hnm hmX

/-- A positive weighted arithmetic row bound gives its logarithmic-square
counterpart with the explicit multiplier `log(X)^2`. -/
theorem weighted_logSquare_row_bound (X : ℕ)
    (B : ℕ → ℕ → ℂ) (w : ℕ → ℝ) (K_0 : ℝ)
    (hw : ∀ m ∈ (Finset.Icc 1 X : Finset ℕ), 0 < w m)
    (hrow0 : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      (∑ m ∈ (Finset.Icc 1 X : Finset ℕ), ‖B n m‖ * w m) ≤ K_0 * w n) :
    ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      (∑ m ∈ (Finset.Icc 1 X : Finset ℕ),
        ‖B n m‖ * logSquareEnvelope n m * w m) ≤
          (Real.log (X : ℝ) ^ 2 * K_0) * w n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnX⟩
  calc
    (∑ m ∈ (Finset.Icc 1 X : Finset ℕ),
        ‖B n m‖ * logSquareEnvelope n m * w m) ≤
        ∑ m ∈ (Finset.Icc 1 X : Finset ℕ),
          Real.log (X : ℝ) ^ 2 * (‖B n m‖ * w m) := by
      apply Finset.sum_le_sum
      intro m hm
      rcases Finset.mem_Icc.mp hm with ⟨hm1, hmX⟩
      have hlog := logSquareEnvelope_le_log_sq hn1 hm1 hnX hmX
      calc
        ‖B n m‖ * logSquareEnvelope n m * w m =
            (‖B n m‖ * w m) * logSquareEnvelope n m := by ring
        _ ≤ (‖B n m‖ * w m) * Real.log (X : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg (norm_nonneg _) (hw m hm).le)
        _ = Real.log (X : ℝ) ^ 2 * (‖B n m‖ * w m) := by ring
    _ = Real.log (X : ℝ) ^ 2 *
        (∑ m ∈ (Finset.Icc 1 X : Finset ℕ), ‖B n m‖ * w m) := by
      rw [Finset.mul_sum]
    _ ≤ Real.log (X : ℝ) ^ 2 * (K_0 * w n) :=
      mul_le_mul_of_nonneg_left
        (hrow0 n (Finset.mem_Icc.mpr ⟨hn1, hnX⟩)) (sq_nonneg _)
    _ = (Real.log (X : ℝ) ^ 2 * K_0) * w n := by ring

end RiemannResearch.Analysis.ActualPrimePowerWeightedRows
