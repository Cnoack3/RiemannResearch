import RiemannResearch.RH.DyadicRegularizedBoundaryEnergy
import RiemannResearch.RH.DyadicRegularizedNormReduction
import RiemannResearch.RH.DyadicFiniteBoundaryCoordinates

/-!
# Complete boundary coordinates and the uniform norm criterion

Source: user-provided DyadicSignedMeanEnergyVerification20260910(1).md,
September 10, 2026. The complete boundary energy, with canonical coefficients
of boundaries of squared norm one quarter, is equivalent to bounding every
finite set by the same constant. The application to the actual normalization
remainder is a conditional research reduction: the uniform arithmetic
estimate remains open. A bound on a single finite prefix is insufficient.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem dyadicBoundaryCoordinate_square_summable (f : ThresholdHilbert) :
    Summable (fun i : ℕ => (1 / 4 : ℝ) * dyadicBoundaryCoordinate f i ^ 2) := by
  apply (dyadicBoundary_mixed_pairings_summable f f).congr
  intro i
  dsimp [dyadicBoundaryCoordinate, dyadicBoundaryVector]
  ring

/-- This is an actual convergent infinite square sum, with its exact factor. -/
theorem dyadicBoundaryDetailEnergy_eq_coordinate_square (f : ThresholdHilbert) :
    dyadicBoundaryDetailEnergy f =
      ∑' i : ℕ, (1 / 4 : ℝ) * dyadicBoundaryCoordinate f i ^ 2 := by
  unfold dyadicBoundaryDetailEnergy
  apply tsum_congr
  intro i
  dsimp [dyadicBoundaryCoordinate, dyadicBoundaryVector]
  ring

/-- All finite sets must share the same bound; the cutoff is universally quantified. -/
theorem dyadicBoundaryDetailEnergy_le_iff_finite_sums
    (f : ThresholdHilbert) (C : ℝ) :
    dyadicBoundaryDetailEnergy f ≤ C ↔
      ∀ s : Finset ℕ, (∑ i ∈ s, (1 / 4 : ℝ) * dyadicBoundaryCoordinate f i ^ 2) ≤ C := by
  rw [dyadicBoundaryDetailEnergy_eq_coordinate_square]
  have hs := dyadicBoundaryCoordinate_square_summable f
  constructor
  · intro h s
    exact (hs.sum_le_tsum s (fun i _ => by positivity)).trans h
  · intro h
    exact le_of_tendsto hs.hasSum (Filter.Eventually.of_forall h)

/-- A bound on the full actual remainder energy supplies both previously named
norm obligations. Convergence and scalar normalization are already proved. -/
theorem dyadicRegularized_norm_obligations_of_boundary_energy
    (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      dyadicBoundaryDetailEnergy (dyadicNormalizationRemainder ε) ≤ C) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound ∧
      DyadicTailRegularizedSeriesSummable ∧ DyadicTailRegularizedNormBound := by
  apply dyadicRegularized_norm_obligations_of_bounded_error
    (Real.sqrt C) (Real.sqrt_nonneg C)
  intro ε hε hhalf
  have hb := henergy ε hε hhalf
  rw [← dyadicNormalizationRemainder_norm_sq_eq_boundary ε hε] at hb
  change ‖dyadicNormalizationRemainder ε‖ ≤ Real.sqrt C
  nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C,
    norm_nonneg (dyadicNormalizationRemainder ε)]

/-- The complete boundary energy is bounded by the actual physical norm. -/
theorem dyadicBoundaryCoordinate_square_tsum_le_norm_sq (f : ThresholdHilbert) :
    (∑' i : ℕ, (1/4 : ℝ) * dyadicBoundaryCoordinate f i ^ 2) ≤ ‖f‖^2 := by
  have hp := dyadicQuotientProjection_pythagoras f
  have hb := dyadicBoundary_parseval_norm_sq f
  have he : (∑' i : ℕ, (1/4 : ℝ) * dyadicBoundaryCoordinate f i ^ 2) =
      ∑' n : ℕ, 4 * (inner ℝ (dyadicQuotientProjection
        (dyadicStepBoundary (n+1) (by positivity))) f)^2 := by
    apply tsum_congr
    intro i
    dsimp [dyadicBoundaryCoordinate, dyadicBoundaryVector]
    ring
  rw [he]
  nlinarith [sq_nonneg (inner ℝ hilbertOne f), sq_nonneg ‖f-dyadicQuotientProjection f‖]

end
end RiemannResearch.RH.Pareto
