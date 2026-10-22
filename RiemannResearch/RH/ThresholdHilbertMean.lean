import RiemannResearch.RH.ThresholdHilbertDilation

/-!
# The weighted inner product, target vector, and adjoint fixed constant

Source: Christian Noack, RH_Two_Seed_Threshold.tex, September 8, 2026,
Sections 1, 2 and 4. All assertions refer to the genuine bundled weighted H.
The reverse joint-adjoint rigidity assertion is not assumed or proved here.
-/
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem hilbert_inner_weighted (f g : ThresholdHilbert) :
    inner ℝ f g = paretoInner (hilbertSequence f) (hilbertSequence g) := by
  have hs := weighted_product_summable_of_square
    (hilbertSequence_square_summable f) (hilbertSequence_square_summable g)
  unfold paretoInner
  rw [hs.tsum_eq_zero_add]
  simp only [hilbertSequence_zero, mul_zero, zero_mul, zero_add]
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [RCLike.inner_apply']
  change f n * g n = positiveWeight (n+1) *
    (hilbertSequence f (n+1) * hilbertSequence g (n+1))
  rw [positiveWeight_succ, hilbertSequence_succ, hilbertSequence_succ,
    div_mul_div_comm, ← pow_two, Real.sq_sqrt (by unfold paretoWeight; positivity)]
  have hw : paretoWeight n ≠ 0 := by unfold paretoWeight; positivity
  field_simp

private theorem target_square_summable :
    Summable (fun k => positiveWeight k * (zeroAnchor (fun _ => (1 : ℝ)) k)^2) := by
  apply positiveWeight_summable.congr
  intro k
  by_cases hk : k = 0
  · subst k; norm_num [zeroAnchor, positiveWeight]
  · simp [zeroAnchor, hk]

/-- The actual target 1 on positive indices; zero is anchored by convention. -/
def hilbertOne : ThresholdHilbert :=
  sequenceHilbert (zeroAnchor (fun _ => (1 : ℝ))) target_square_summable

@[simp] theorem hilbertOne_sequence :
    hilbertSequence hilbertOne = zeroAnchor (fun _ => (1 : ℝ)) := by
  apply hilbertSequence_sequenceHilbert
  simp [zeroAnchor]

theorem hilbertOne_norm_sq : ‖hilbertOne‖^2 = 1 := by
  rw [hilbert_norm_weighted_sq, hilbertOne_sequence]
  have he : (fun k => positiveWeight k * (zeroAnchor (fun _ => (1 : ℝ)) k)^2) =
      positiveWeight := by
    funext k
    by_cases hk : k = 0
    · subst k; norm_num [zeroAnchor, positiveWeight]
    · simp [zeroAnchor, hk]
  rw [he, positiveWeight_tsum]

/-- Expectation is precisely pairing with the fixed Hilbert target. -/
theorem hilbert_inner_one (f : ThresholdHilbert) :
    inner ℝ f hilbertOne = paretoMean (hilbertSequence f) := by
  rw [hilbert_inner_weighted, hilbertOne_sequence]
  unfold paretoInner paretoMean
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · subst k; simp
  · simp [zeroAnchor, hk]

/-- The concrete adjoint fixes the constant target for every positive integer. -/
theorem hilbertDilationAdjoint_one (m : ℕ) (hm : 0 < m) :
    hilbertDilationAdjoint m hm hilbertOne = hilbertOne := by
  apply ext_inner_left ℝ
  intro f
  change inner ℝ f ((hilbertDilationContinuous m hm).adjoint hilbertOne) = _
  rw [ContinuousLinearMap.adjoint_inner_right, hilbert_inner_one, hilbert_inner_one]
  exact hilbertDilation_mean m hm f

end
end RiemannResearch.RH.Pareto
