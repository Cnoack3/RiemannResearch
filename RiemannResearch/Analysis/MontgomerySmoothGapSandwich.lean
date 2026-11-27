import RiemannResearch.Analysis.MontgomeryAllPairWordLimit
import RiemannResearch.Analysis.MontgomerySampledCountError
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Recovering cumulative PCC by smooth tests of all strictly positive gaps

Even smooth cutoffs equal to one on a smaller centered interval and zero
outside a larger interval suffice. The empirical sum uses every strictly
positive ordinate gap, with multiplicities. Ties are absent even where the
cutoff function is one near zero. -/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryAllPairWordRounding
open ActualZeroOrdinate MontgomeryPositiveGap

private def pairDensity (x : ℝ) : ℝ := 1 - Real.sinc (Real.pi*x)^2

private lemma density_nonneg (x : ℝ) : 0 ≤ pairDensity x := by
  dsimp [pairDensity]
  have h := abs_le.mp (Real.abs_sinc_le_one (Real.pi*x))
  nlinarith [mul_nonneg (show 0 ≤ 1 - Real.sinc (Real.pi*x) by linarith [h.2])
    (show 0 ≤ 1 + Real.sinc (Real.pi*x) by linarith [h.1])]

private lemma density_continuous : Continuous pairDensity := by
  change Continuous (fun x : ℝ => 1 - Real.sinc (Real.pi * x)^2)
  fun_prop

private lemma test_mono {T : ℝ} (hT : 1 < T) {f g : ℝ → ℝ}
    (h : ∀ x, 0 < x → f x ≤ g x) : actualPositiveTest T f ≤ actualPositiveTest T g := by
  unfold actualPositiveTest positiveTestSum
  apply div_le_div_of_nonneg_right _
    (div_nonneg (mul_nonneg (zero_lt_one.trans hT).le (Real.log_pos hT).le) (by positivity))
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hx
  · exact h _ (mul_pos (div_pos (Real.log_pos hT) (by positivity)) (sub_pos.mpr hx))
  · exact le_rfl

private lemma test_cutoff_eq (T q : ℝ) (hT : 1 < T) :
    actualPositiveTest T (fun x => if x ≤ q then 1 else 0) = positiveGapMass T q := by
  unfold actualPositiveTest positiveTestSum positiveGapMass
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let a := Real.log T / (2 * Real.pi)
  have ha : 0 < a := div_pos (Real.log_pos hT) (by positivity)
  change (if copyOrdinate T i < copyOrdinate T j then
    if a * (copyOrdinate T j-copyOrdinate T i) ≤ q then (1 : ℝ) else 0 else 0) =
    if 0 < a * (copyOrdinate T j-copyOrdinate T i) ∧
       a * (copyOrdinate T j-copyOrdinate T i) ≤ q then 1 else 0
  simp only [mul_pos_iff_of_pos_left ha, sub_pos]
  split_ifs <;> grind

theorem actualPositiveTest_bump_bounds {T : ℝ} (hT : 1 < T) (b : ContDiffBump (0 : ℝ)) :
    positiveGapMass T b.rIn ≤ actualPositiveTest T b ∧
      actualPositiveTest T b ≤ positiveGapMass T b.rOut := by
  rw [← test_cutoff_eq T b.rIn hT, ← test_cutoff_eq T b.rOut hT]
  constructor
  · apply test_mono hT
    intro x hx
    by_cases hin : x ≤ b.rIn
    · rw [if_pos hin, b.one_of_mem_closedBall (by
        simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_pos hx] using hin)]
    · simpa [hin] using b.nonneg' x
  · apply test_mono hT
    intro x hx
    by_cases hout : x ≤ b.rOut
    · simpa [hout] using (b.le_one (x := x))
    · rw [if_neg hout, b.zero_of_le_dist (by
        simpa [Real.dist_eq, abs_of_pos hx] using (le_of_lt (lt_of_not_ge hout)))]

private lemma model_bump_bounds (b : ContDiffBump (0 : ℝ)) :
    sineGapMass b.rIn ≤ (∫ x in (0 : ℝ)..b.rOut, b x * pairDensity x) ∧
      (∫ x in (0 : ℝ)..b.rOut, b x * pairDensity x) ≤ sineGapMass b.rOut := by
  have hc : Continuous (fun x : ℝ => b x * pairDensity x) := b.continuous.mul density_continuous
  constructor
  · have he : (∫ x in (0 : ℝ)..b.rIn, b x * pairDensity x) = sineGapMass b.rIn := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le b.rIn_pos.le] at hx
      change b x * pairDensity x = pairDensity x
      rw [b.one_of_mem_closedBall (x := x) (by
          simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg hx.1] using hx.2), one_mul]
    rw [← he, ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (0 : ℝ) b.rIn) (hc.intervalIntegrable b.rIn b.rOut)]
    exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg b.rIn_lt_rOut.le
      (fun x _ => mul_nonneg (b.nonneg' x) (density_nonneg x)))
  · apply intervalIntegral.integral_mono_on b.rOut_pos.le (hc.intervalIntegrable _ _)
      (density_continuous.intervalIntegrable _ _)
    intro x _
    change b x * pairDensity x ≤ pairDensity x
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (b.le_one (x := x)) (density_nonneg x)

/-- Convergence of all centered smooth plateau cutoffs, a subclass of the
even compactly supported smooth tests, suffices for full positive-gap PCC. -/
theorem positiveGapPCC_of_even_bump_limits
    (h : ∀ b : ContDiffBump (0 : ℝ), Tendsto (fun T => actualPositiveTest T b) atTop
      (𝓝 (∫ x in (0 : ℝ)..b.rOut, b x * (1 - Real.sinc (Real.pi*x)^2)))) :
    PositiveGapPCC := by
  apply positiveGapPCC_of_pointwise
  intro q hq
  apply tendsto_order.2
  constructor
  · intro l hl
    obtain ⟨a, ha, haq⟩ := exists_between (show max 0 (q - (sineGapMass q-l)) < q from
      max_lt hq (by linarith only [hl]))
    let b : ContDiffBump (0 : ℝ) := ⟨a,q,(le_max_left _ _).trans_lt ha,haq⟩
    have hlow : l < sineGapMass a := by
      linarith only [(sineGapMass_increment_bounds haq.le).2, (le_max_right _ _).trans_lt ha]
    have hlim := (h b).eventually_const_lt (hlow.trans_le (model_bump_bounds b).1)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with T hval hT
    exact hval.trans_le (actualPositiveTest_bump_bounds hT b).2
  · intro u hu
    obtain ⟨a,hqa,ha⟩ := exists_between (show q < q+(u-sineGapMass q) by linarith only [hu])
    let b : ContDiffBump (0 : ℝ) := ⟨q,a,hq,hqa⟩
    have hhigh : sineGapMass a < u := by linarith only [(sineGapMass_increment_bounds hqa.le).2,ha]
    have hlim := (h b).eventually_lt_const ((model_bump_bounds b).2.trans_lt hhigh)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with T hval hT
    exact ((actualPositiveTest_bump_bounds hT b).1).trans_lt hval

end RiemannResearch.Analysis.MontgomeryAllPairWordRounding
