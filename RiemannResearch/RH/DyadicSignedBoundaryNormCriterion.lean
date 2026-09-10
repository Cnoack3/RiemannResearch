import RiemannResearch.RH.DyadicRegularizedBoundaryCoefficients
import RiemannResearch.RH.DyadicBoundaryUniformCriterion

/-!
# The actual signed arithmetic square-sum obligation

Source: user-provided DyadicSignedMeanEnergyVerification20260910(1).md,
September 10, 2026. The scalar coefficients below are independently identified
with the actual Hilbert vectors in the imported arithmetic module. In
particular the error is not defined by an unrelated surrogate sequence.
The uniform estimate remains an explicit hypothesis, not a supplied provider.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The complete squared signed remainder coefficients are summable at each
positive damping, with no finite-scale truncation. -/
theorem dyadicNormalizationBoundaryCoefficient_square_summable
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun i : ℕ => (1 / 4 : ℝ) *
      dyadicNormalizationBoundaryCoefficient ε i ^ 2) := by
  simpa only [dyadicNormalizationRemainder_boundaryCoordinate hε] using
    dyadicBoundaryCoordinate_square_summable (dyadicNormalizationRemainder ε)

/-- All signed arithmetic and comparison terms remain inside the square. -/
theorem dyadicNormalizationRemainder_norm_sq_eq_signedBoundary
    {ε : ℝ} (hε : 0 < ε) :
    ‖dyadicNormalizationRemainder ε‖ ^ 2 =
      ∑' i : ℕ, (1 / 4 : ℝ) * dyadicNormalizationBoundaryCoefficient ε i ^ 2 := by
  rw [dyadicNormalizationRemainder_norm_sq_eq_boundary ε hε,
    dyadicBoundaryDetailEnergy_eq_coordinate_square]
  simp only [dyadicNormalizationRemainder_boundaryCoordinate hε]

/-- The full approximation error of the actual projected family. -/
theorem dyadicRegularizedFamily_error_sq_eq_signedBoundary
    {ε : ℝ} (hε : 0 < ε) :
    ‖dyadicRegularizedFamily ε - hilbertOne‖ ^ 2 =
      ∑' i : ℕ, (1 / 4 : ℝ) * dyadicSignedBoundaryCoefficient ε i ^ 2 := by
  rw [dyadicRegularizedFamily_error_sq_eq_boundary ε hε,
    dyadicBoundaryDetailEnergy_eq_coordinate_square]
  simp only [dyadicRegularizedFamily_boundaryCoordinate hε]

/-- One constant must bound every finite set and every positive damping in
the interval. This conditional reduction supplies the full base and physical
tail norm obligations; it does not supply the arithmetic bound or RH. -/
theorem dyadicRegularized_norm_obligations_of_signedBoundary
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ s : Finset ℕ,
      (∑ i ∈ s, (1 / 4 : ℝ) * dyadicNormalizationBoundaryCoefficient ε i ^ 2) ≤ C) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound ∧
      DyadicTailRegularizedSeriesSummable ∧ DyadicTailRegularizedNormBound := by
  apply dyadicRegularized_norm_obligations_of_boundary_energy C hC
  intro ε hε hhalf
  apply (dyadicBoundaryDetailEnergy_le_iff_finite_sums _ C).mpr
  intro s
  simpa only [dyadicNormalizationRemainder_boundaryCoordinate hε] using
    hbound ε hε hhalf s

end
end RiemannResearch.RH.Pareto
