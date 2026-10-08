import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.ParetoGibbsGammaDefect
import RiemannResearch.RH.ParetoComparableWeights

/-!
# A mean gap forces large error after exact head interpolation

Source: user-directed research continuation; see
`IndependentPrimeResearchContinuation20261007.md` for the statements
and their mathematical interpretation.


An error vanishing on physical coordinates 1 through N has its complete mean
supported in the Pareto tail of mass 1/(N+1). Cauchy--Schwarz therefore gives
an unconditional lower bound for its full squared norm. The last theorem
transfers this bound to inverse-square weights with any positive normalization.
There is no RH hypothesis, legal-span assumption, or arithmetic provider.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ExactHeadMeanGap

theorem tailOne_norm_sq (N : ℕ) :
    ‖hilbertTailShift hilbertOne N‖ ^ 2 = 1 / ((N : ℝ) + 1) := by
  rw [hilbert_norm_sq]
  change (∑' n : ℕ, (hilbertOne (n + N)) ^ 2) = _
  calc
    _ = ∑' n : ℕ, paretoWeight (n + N) := by
      apply tsum_congr
      intro n
      have hone : hilbertSequence hilbertOne (n + N + 1) = 1 := by
        rw [hilbertOne_sequence]
        simp [zeroAnchor]
      rw [← hilbertSequence_weighted_square hilbertOne (n + N),
        hone, one_pow, mul_one, positiveWeight_succ]
    _ = _ := paretoWeight_shift_tsum N

/-- Exact physical head interpolation forces the corresponding bundled error
coordinates to vanish. The square-root weight is strictly positive. -/
theorem error_coordinate_eq_zero (N : ℕ) (f : ThresholdHilbert)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    ∀ n < N, (hilbertOne - f) n = 0 := by
  intro n hn
  have hs := hhead (n + 1) (by omega) (by omega)
  have hone : hilbertSequence hilbertOne (n + 1) = 1 := by
    rw [hilbertOne_sequence]
    simp [zeroAnchor]
  have hsame : hilbertSequence hilbertOne (n + 1) =
      hilbertSequence f (n + 1) := hone.trans hs.symm
  have hw : Real.sqrt (paretoWeight n) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    unfold paretoWeight
    positivity
  have hc : hilbertOne n = f n := (div_left_inj' hw).mp hsame
  change hilbertOne n - f n = 0
  exact sub_eq_zero.mpr hc

/-- Complete Pareto error, including the entire infinite tail, is bounded below
by (N+1) times the square of the exact mean defect. -/
theorem error_sq_ge_mean_gap (N : ℕ) (f : ThresholdHilbert)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    ((N : ℝ) + 1) * (1 - paretoMean (hilbertSequence f)) ^ 2 ≤
      ‖hilbertOne - f‖ ^ 2 := by
  have h := hilbertTailShift_inner_sq_le hilbertOne (hilbertOne - f) N
    (error_coordinate_eq_zero N f hhead)
  have hcomm : inner ℝ hilbertOne f = inner ℝ f hilbertOne :=
    real_inner_comm _ _
  have hmean : inner ℝ hilbertOne (hilbertOne - f) =
      1 - paretoMean (hilbertSequence f) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
      hcomm, hilbert_inner_one]
  rw [hmean, tailOne_norm_sq] at h
  have hdiv : (1 - paretoMean (hilbertSequence f)) ^ 2 ≤
      ‖hilbertOne - f‖ ^ 2 / ((N : ℝ) + 1) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h
  have hc := (le_div_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mp hdiv
  simpa only [mul_comm] using hc

/-- With Z = zeta(2), these are the zeta-law probabilities on physical n+1. -/
def normalizedInverseSquareWeight (Z : ℝ) (n : ℕ) : ℝ :=
  ComparableWeights.inverseSquareWeight n / Z

theorem normalizedEnergy_ge_pareto (Z : ℝ) (hZ : 0 < Z)
    (e : ThresholdHilbert) :
    (1 / Z) * ‖e‖ ^ 2 ≤
      ComparableWeights.weightedEnergy (normalizedInverseSquareWeight Z) e := by
  refine ComparableWeights.weightedEnergy_ge
    (normalizedInverseSquareWeight Z) (1 / Z) (2 / Z) ?_ ?_ ?_ e
  · intro n
    unfold normalizedInverseSquareWeight ComparableWeights.inverseSquareWeight
    positivity
  · intro n
    unfold normalizedInverseSquareWeight
    have h := div_le_div_of_nonneg_right
      (ComparableWeights.paretoWeight_le_inverseSquareWeight n) hZ.le
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h
  · intro n
    unfold normalizedInverseSquareWeight
    have h := div_le_div_of_nonneg_right
      (ComparableWeights.inverseSquareWeight_le_twice_paretoWeight n) hZ.le
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- The mean obstruction transferred to the complete normalized inverse-square
energy. Specializing Z to zeta(2) gives the independent-prime law version. -/
theorem normalizedError_ge_mean_gap (Z : ℝ) (hZ : 0 < Z)
    (N : ℕ) (f : ThresholdHilbert)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    (((N : ℝ) + 1) / Z) * (1 - paretoMean (hilbertSequence f)) ^ 2 ≤
      ComparableWeights.weightedEnergy (normalizedInverseSquareWeight Z)
        (hilbertOne - f) := by
  calc
    _ = (1 / Z) * (((N : ℝ) + 1) *
        (1 - paretoMean (hilbertSequence f)) ^ 2) := by ring
    _ ≤ (1 / Z) * ‖hilbertOne - f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (error_sq_ge_mean_gap N f hhead) (by positivity)
    _ ≤ _ := normalizedEnergy_ge_pareto Z hZ (hilbertOne - f)

end RiemannResearch.RH.Pareto.ExactHeadMeanGap
