import RiemannResearch.Analysis.DiscreteTailHardy
import RiemannResearch.RH.ParetoSignedTailRegularity

/-!
# Automatic square summability of signed Pareto primitives

Source: user-provided argument, Section 25.5 of
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`.
The only input is the actual weighted square summability of the original
sequence. Neither a Hardy bound nor primitive summability is assumed.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace RiemannResearch.RH.Pareto

/-- The pointwise form of the manuscript's tail Cauchy--Schwarz estimate. -/
theorem abs_signedTail_le_sqrt_tailEnergy {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (n : ℕ) (hn : 0 < n) :
    |signedTail h n| ≤ Real.sqrt (signedTailEnergy h n) / Real.sqrt (n : ℝ) := by
  have hnp : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hn)
  apply (le_div_iff₀ hnp).2
  have hh := Real.sqrt_le_sqrt (signedTail_mul_sq_le_tailEnergy hs n hn)
  rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs] at hh
  simpa only [mul_comm] using hh

/-- The unsquared vanishing statement sqrt(n) A_n → 0. -/
theorem signedTail_sqrt_mul_tendsto_zero {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * signedTail h n)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have he (n : ℕ) : ‖Real.sqrt (n : ℝ) * signedTail h n‖ =
      Real.sqrt ((n : ℝ) * signedTail h n ^ 2) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs]
  have ht := (Real.continuous_sqrt.tendsto 0).comp
    (signedTail_mul_sq_tendsto_zero hs)
  simpa only [he, Function.comp_def, Real.sqrt_zero] using ht

private theorem signedTail_difference_square_le {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ 2 * (signedTail h n - signedTail h (n + 1)) ^ 2 ≤
      positiveWeight n * h n ^ 2 := by
  have he := anchoredSignedTail_energy_density hs n
  rw [anchoredSignedTail_pos h hn,
    anchoredSignedTail_pos h (Nat.succ_pos n)] at he
  have hp := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    (sq_nonneg (signedTail h n - signedTail h (n + 1)))
  nlinarith

/-- Actual Pareto H membership automatically supplies l² for the primitive. -/
theorem signedTail_positive_square_summable {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Summable (fun k => signedTail h (k + 1) ^ 2) :=
  RiemannResearch.Analysis.DiscreteTailHardy.positive_square_summable
    (signedTail h) (fun k => positiveWeight k * h k ^ 2) hs
    (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
    (signedTail_difference_square_le hs) (signedTail_mul_sq_tendsto_zero hs)

/-- The exact constant-four estimate of the manuscript, indexed from one. -/
theorem signedTail_positive_square_tsum_le {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    (∑' k, signedTail h (k + 1) ^ 2) ≤
      4 * ∑' k, positiveWeight k * h k ^ 2 :=
  RiemannResearch.Analysis.DiscreteTailHardy.positive_square_tsum_le
    (signedTail h) (fun k => positiveWeight k * h k ^ 2) hs
    (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
    (signedTail_difference_square_le hs) (signedTail_mul_sq_tendsto_zero hs)

theorem signedTail_square_summable {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Summable (fun k => signedTail h k ^ 2) :=
  (summable_nat_add_iff 1).mp (signedTail_positive_square_summable hs)

/-- The conventional zero-anchored primitive is square summable as well. -/
theorem anchoredSignedTail_square_summable {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Summable (fun k => anchoredSignedTail h k ^ 2) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [anchoredSignedTail_pos h (Nat.succ_pos _)] using
    signedTail_positive_square_summable hs

/-- Anchoring at zero removes the spurious duplicate mean coordinate. -/
theorem anchoredSignedTail_square_tsum_le {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    (∑' k, anchoredSignedTail h k ^ 2) ≤
      4 * ∑' k, positiveWeight k * h k ^ 2 := by
  have he := (anchoredSignedTail_square_summable hs).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, anchoredSignedTail_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, anchoredSignedTail_pos h (Nat.succ_pos _)] at he
  rw [← he]
  exact signedTail_positive_square_tsum_le hs

end RiemannResearch.RH.Pareto
