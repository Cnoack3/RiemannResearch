import RiemannResearch.RH.NaturalMobiusDerivativeTests
import RiemannResearch.NumberTheory.DivisorCountSquareSummability

/-!
# Strong convergence of the full natural-cutoff Möbius derivative

The elementary divisor-square majorant upgrades the established coordinate
limits to convergence in the complete Pareto Hilbert norm. The exact
canonical correction identity is retained: its derivative tends to the
negative limiting canonical derivative residual, not necessarily to zero.

Source: the user-directed vanishing attempt and the repository's actual PNT,
natural Möbius, divisor-count, and projection-limit declarations.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto

theorem summable_weighted_one_add_divisor_count_sq :
    Summable (fun k : ℕ => positiveWeight k * (1 + (k.divisors.card : ℝ)) ^ 2) := by
  apply RiemannResearch.NumberTheory.summable_one_add_divisor_count_sq_div_sq.of_nonneg_of_le
  · intro k
    exact mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)
  · intro k
    by_cases hk : k = 0
    · simp [hk, positiveWeight]
    have hkR : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    change (1 / ((k : ℝ) * ((k : ℝ) + 1))) *
      (1 + (k.divisors.card : ℝ)) ^ 2 ≤ _
    rw [one_div, inv_mul_eq_div]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hkR)
    nlinarith

/-- The complete infinite weighted square, with every coordinate retained,
converges to zero along all natural cutoffs. -/
theorem rawMobiusDerivativeResidual_norm_sq_tendsto_zero :
    Tendsto (fun N => ‖rawMobiusDerivativeResidual N‖ ^ 2) atTop (𝓝 0) := by
  have hp : ∀ k, Tendsto
      (fun N => positiveWeight k *
        (hilbertSequence (rawMobiusDerivativeResidual N) k) ^ 2) atTop (𝓝 0) := by
    intro k
    simpa using ((rawMobiusDerivativeResidual_coordinate_tendsto_zero k).pow 2).const_mul
      (positiveWeight k)
  have hb : ∀ᶠ N : ℕ in atTop, ∀ k,
      ‖positiveWeight k * (hilbertSequence (rawMobiusDerivativeResidual N) k) ^ 2‖ ≤
      positiveWeight k * (1 + (k.divisors.card : ℝ)) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
    have ha := rawMobiusDerivativeResidual_abs_le N hN k
    have hs := mul_le_mul ha ha
      (abs_nonneg (hilbertSequence (rawMobiusDerivativeResidual N) k))
      (show 0 ≤ 1 + (k.divisors.card : ℝ) by positivity)
    simpa only [← pow_two, sq_abs] using hs
  have ht := tendsto_tsum_of_dominated_convergence
    summable_weighted_one_add_divisor_count_sq hp hb
  simpa only [← hilbert_norm_weighted_sq, tsum_zero] using ht

theorem rawMobiusDerivativeResidual_norm_tendsto_zero :
    Tendsto (fun N => ‖rawMobiusDerivativeResidual N‖) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    rawMobiusDerivativeResidual_norm_sq_tendsto_zero
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- Actual Hilbert convergence, strengthening every bounded-test conclusion. -/
theorem rawMobiusDerivativeResidual_tendsto_zero :
    Tendsto rawMobiusDerivativeResidual atTop (𝓝 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    rawMobiusDerivativeResidual_norm_tendsto_zero

/-- Every fixed Hilbert test is now allowed; no physical boundedness premise remains. -/
theorem rawMobiusDerivativeResidual_inner_tendsto_zero (f : ThresholdHilbert) :
    Tendsto (fun N => inner ℝ f (rawMobiusDerivativeResidual N)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    ((innerSL ℝ f).continuous.tendsto 0).comp rawMobiusDerivativeResidual_tendsto_zero

namespace CoefficientStabilization.DerivativeCompatibility
open GramMobiusCorrection

/-- Differentiation preserves the complete canonical correction with its sign. -/
theorem derivative_correction_exact (n : ℕ) :
    hilbertDifference (correctionSynthesis n) =
      rawMobiusDerivativeResidual (n + 1) - derivativeResidual n := by
  rw [rawMobiusDerivativeResidual_eq_mobiusResidual, derivativeResidual,
    ← mobiusResidual_sub_correction n, map_sub]
  abel

/-- The original Gram correction has an unconditional strong derivative limit.
The limit is identified exactly; its vanishing is not asserted. -/
theorem derivative_correction_tendsto :
    Tendsto (fun n => hilbertDifference (correctionSynthesis n)) atTop
      (𝓝 (-hilbertDifference limitResidual)) := by
  have hraw := rawMobiusDerivativeResidual_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, derivative_correction_exact, zero_sub] using
    hraw.sub derivativeResidual_tendsto

/-- Exact signed cancellation, including both complete quadratic energies. -/
theorem raw_derivative_complete_correction_energy (n : ℕ) :
    ‖rawMobiusDerivativeResidual (n + 1)‖ ^ 2 =
      ‖derivativeResidual n‖ ^ 2 +
      2 * inner ℝ (derivativeResidual n) (hilbertDifference (correctionSynthesis n)) +
      ‖hilbertDifference (correctionSynthesis n)‖ ^ 2 := by
  have he : rawMobiusDerivativeResidual (n + 1) =
      derivativeResidual n + hilbertDifference (correctionSynthesis n) := by
    rw [derivative_correction_exact]
    abel
  rw [he, norm_add_sq_real]

theorem derivative_correction_norm_sq_tendsto :
    Tendsto (fun n => ‖hilbertDifference (correctionSynthesis n)‖ ^ 2) atTop
      (𝓝 (‖hilbertDifference limitResidual‖ ^ 2)) := by
  simpa only [norm_neg] using derivative_correction_tendsto.norm.pow 2

/-- The signed cross term cancels both limiting quadratic energies exactly. -/
theorem derivative_correction_cross_tendsto :
    Tendsto (fun n => inner ℝ (derivativeResidual n)
      (hilbertDifference (correctionSynthesis n))) atTop
      (𝓝 (-‖hilbertDifference limitResidual‖ ^ 2)) := by
  simpa only [inner_neg_right, real_inner_self_eq_norm_sq] using
    derivativeResidual_tendsto.inner (𝕜 := ℝ) derivative_correction_tendsto

end CoefficientStabilization.DerivativeCompatibility
end RiemannResearch.RH.Pareto
