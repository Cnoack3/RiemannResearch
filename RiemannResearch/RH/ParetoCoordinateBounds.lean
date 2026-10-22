import RiemannResearch.RH.ParetoCoordinateEvaluation

/-!
# Full Pareto norm bounds for physical coordinates

Source: user-provided Pareto projection proof, 22 September 2026,
equation (1). These bounds use the complete infinite weighted norm.
They are kept separately from the evaluation-map definitions so that
additional inequalities do not invalidate that shared dependency chain.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Every weighted physical coordinate is bounded by the entire squared norm. -/
theorem hilbertSequence_weighted_sq_le (f : ThresholdHilbert) (n : ℕ) :
    positiveWeight n * (hilbertSequence f n)^2 ≤ ‖f‖^2 := by
  rw [hilbert_norm_weighted_sq]
  simpa only [Finset.sum_singleton] using
    (hilbertSequence_square_summable f).sum_le_tsum ({n} : Finset ℕ)
      (fun k _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))

/-- The literal coordinate square bound from the manuscript, including anchored zero. -/
theorem hilbertSequence_sq_le_norm_sq (f : ThresholdHilbert) (n : ℕ) :
    (hilbertSequence f n)^2 ≤ (n : ℝ) * ((n : ℝ) + 1) * ‖f‖^2 := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hden : 0 < (n : ℝ) * ((n : ℝ) + 1) := by positivity
  have h := hilbertSequence_weighted_sq_le f n
  have hdiv : (hilbertSequence f n)^2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ ‖f‖^2 := by
    simpa only [positiveWeight, one_div, div_eq_mul_inv, one_mul, mul_comm] using h
  have hmul := (div_le_iff₀ hden).mp hdiv
  nlinarith only [hmul]


end
end RiemannResearch.RH.Pareto
