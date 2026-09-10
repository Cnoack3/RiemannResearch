import RiemannResearch.RH.DyadicRegularizedMean
import RiemannResearch.RH.DyadicBoundaryLegalRecovery
import RiemannResearch.RH.DyadicStepLogBound

/-!
# Exact centered boundary energy of the actual arithmetic regularization

Source: user-provided DyadicAllScaleConvergenceVerification20260910(2).md,
September 10, 2026, actual normalization remainder and full legal-recovery
frontier. Uses the independently derived mean theorem, with Mathlib's
unconditional Möbius Dirichlet inversion, and the complete physical boundary
Parseval theorem. The projected family has mean one and no complementary
component. Membership of this projected family in the full legal closure is
not asserted. A norm or boundary-energy bound is not proved here.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The convergent arithmetic family is genuinely in the dyadic quotient. -/
theorem dyadicRegularizedFamily_projection (ε : ℝ) (hε : 0 < ε) :
    dyadicQuotientProjection (dyadicRegularizedFamily ε) =
      dyadicRegularizedFamily ε := by
  have hs := dyadicRegularizedTerm_summable hε
  unfold dyadicRegularizedFamily
  rw [map_smul, dyadicQuotientProjection.map_tsum hs]
  congr 1
  apply tsum_congr
  intro p
  simp only [dyadicRegularizedTerm, map_smul,
    dyadicQuotientProjection_idempotent]

/-- Every quotient detail remains in the complete convergent boundary sum. -/
theorem dyadicRegularizedFamily_norm_sq_eq_boundary (ε : ℝ) (hε : 0 < ε) :
    ‖dyadicRegularizedFamily ε‖^2 =
      1 + dyadicBoundaryDetailEnergy (dyadicRegularizedFamily ε) := by
  have h := dyadicBoundary_parseval_norm_sq (dyadicRegularizedFamily ε)
  rw [dyadicRegularizedFamily_projection ε hε,
    real_inner_comm (dyadicRegularizedFamily ε) hilbertOne,
    dyadicRegularizedFamily_inner_one ε hε,
    one_pow] at h
  exact h

/-- The actual target error is exactly the complete centered boundary energy. -/
theorem dyadicRegularizedFamily_error_sq_eq_boundary (ε : ℝ) (hε : 0 < ε) :
    ‖dyadicRegularizedFamily ε - hilbertOne‖^2 =
      dyadicBoundaryDetailEnergy (dyadicRegularizedFamily ε) := by
  have hnorm := dyadicRegularizedFamily_norm_sq_eq_one_add_error ε hε
  have hboundary := dyadicRegularizedFamily_norm_sq_eq_boundary ε hε
  linarith

/-- The exact comparison vector specified by the continuation handoff. -/
def dyadicNormalizationComparison (ε : ℝ) : ThresholdHilbert :=
  dyadicQuotientProjection hilbertOne +
    (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
      dyadicStepAbelOrbit ε

/-- The actual remainder; its full vector estimate is still an open input. -/
def dyadicNormalizationRemainder (ε : ℝ) : ThresholdHilbert :=
  dyadicRegularizedFamily ε - dyadicNormalizationComparison ε

theorem dyadicNormalizationComparison_inner_one (ε : ℝ) (hε : 0 < ε) :
    inner ℝ (dyadicNormalizationComparison ε) hilbertOne = 1 := by
  have hstep := dyadicStepAbelOrbit_inner_one ε hε
    (dyadicStepAbelOrbit_series_summable ε hε)
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [dyadicNormalizationComparison, inner_sub_left, inner_add_left,
    real_inner_smul_left, dyadicQuotientProjection_inner_one,
    dyadicQuotientProjection_inner_one, real_inner_self_eq_norm_sq,
    hilbertOne_norm_sq, hilbertResidue_inner_one, hstep]
  norm_num only [Nat.cast_ofNat]
  rw [inv_mul_cancel₀ hlog]
  norm_num

/-- Scalar normalization has no remainder: all unresolved error is mean zero. -/
theorem dyadicNormalizationRemainder_inner_one (ε : ℝ) (hε : 0 < ε) :
    inner ℝ (dyadicNormalizationRemainder ε) hilbertOne = 0 := by
  rw [dyadicNormalizationRemainder, inner_sub_left,
    dyadicRegularizedFamily_inner_one ε hε,
    dyadicNormalizationComparison_inner_one ε hε, sub_self]

theorem dyadicNormalizationComparison_projection (ε : ℝ) (hε : 0 < ε) :
    dyadicQuotientProjection (dyadicNormalizationComparison ε) =
      dyadicNormalizationComparison ε := by
  have hs := dyadicStepAbelOrbit_series_summable ε hε
  unfold dyadicNormalizationComparison dyadicStepAbelOrbit
  rw [map_sub, map_add, map_smul, map_smul,
    dyadicQuotientProjection_idempotent, dyadicQuotientProjection_idempotent,
    dyadicQuotientProjection.map_tsum hs]
  congr 2
  apply tsum_congr
  intro j
  rw [map_smul, dyadicQuotientProjection_idempotent]

theorem dyadicNormalizationRemainder_projection (ε : ℝ) (hε : 0 < ε) :
    dyadicQuotientProjection (dyadicNormalizationRemainder ε) =
      dyadicNormalizationRemainder ε := by
  rw [dyadicNormalizationRemainder, map_sub,
    dyadicRegularizedFamily_projection ε hε,
    dyadicNormalizationComparison_projection ε hε]

/-- The actual remainder norm is exactly its full infinite boundary energy. -/
theorem dyadicNormalizationRemainder_norm_sq_eq_boundary (ε : ℝ) (hε : 0 < ε) :
    ‖dyadicNormalizationRemainder ε‖ ^ 2 =
      dyadicBoundaryDetailEnergy (dyadicNormalizationRemainder ε) := by
  have h := dyadicBoundary_parseval_norm_sq (dyadicNormalizationRemainder ε)
  rw [dyadicNormalizationRemainder_projection ε hε,
    real_inner_comm (dyadicNormalizationRemainder ε) hilbertOne,
    dyadicNormalizationRemainder_inner_one ε hε, zero_pow (by norm_num : 2 ≠ 0),
    zero_add] at h
  exact h

/-- The complete exact norm expansion retains the signed interaction between
the centered comparison and the actual mean-zero arithmetic remainder. -/
theorem dyadicRegularizedFamily_norm_sq_comparison_remainder
    (ε : ℝ) (hε : 0 < ε) :
    ‖dyadicRegularizedFamily ε‖^2 =
      1 + ‖dyadicNormalizationComparison ε - hilbertOne‖^2 +
        ‖dyadicNormalizationRemainder ε‖^2 +
        2 * inner ℝ (dyadicNormalizationComparison ε - hilbertOne)
          (dyadicNormalizationRemainder ε) := by
  rw [dyadicRegularizedFamily_norm_sq_eq_one_add_error ε hε]
  have he : dyadicRegularizedFamily ε - hilbertOne =
      (dyadicNormalizationComparison ε - hilbertOne) +
        dyadicNormalizationRemainder ε := by
    unfold dyadicNormalizationRemainder
    abel
  rw [he, norm_add_sq_real]
  ring

end
end RiemannResearch.RH.Pareto
