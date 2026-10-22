import RiemannResearch.RH.NaturalMobiusLogarithmicTests
import RiemannResearch.RH.NaturalMobiusSourceLimits
import RiemannResearch.RH.ParetoTailAverages

/-!
# Centered physical primitives of the raw Möbius residual

The constant mode is handled by the proved logarithmic Möbius mean. Hence
the primitive summability condition may be imposed after subtracting any
linear function L K. This extends the unconditional test class, but provides
no estimate for the actual limiting orthogonal residual. The final RH theorem
retains the centered physical primitive condition as an explicit hypothesis.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- The physical coordinate is an exact difference of normalized weighted tails. -/
theorem physicalCoordinate_eq_tailAverage (f : ThresholdHilbert) (n : ℕ) :
    hilbertSequence f (n + 1) =
      ((n : ℝ) + 2) * tailAverage f n -
        ((n : ℝ) + 1) * tailAverage f (n + 1) := by
  have h := hardyCoordinates_reconstruction f n
  rw [hilbertGibbsPhysical_eq, hardyCoordinates_succ,
    hardyCoordinates_partial_sum] at h
  calc
    _ = ((n : ℝ) + 1) * (tailAverage f n - tailAverage f (n + 1)) -
        (-tailAverage f n) := h
    _ = _ := by ring

/-- Physical partial sums and normalized weighted tails are related by this
exact summation-by-parts identity, rather than being the same quantity. -/
theorem physicalPrimitive_eq_tailAverage (f : ThresholdHilbert) (K : ℕ) :
    (∑ k ∈ Finset.range K, hilbertSequence f (k + 1)) =
      2 * (∑ k ∈ Finset.range K, tailAverage f k) - (K : ℝ) * tailAverage f K := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [Finset.sum_range_succ]
    rw [ih, physicalCoordinate_eq_tailAverage]
    push_cast
    ring

/-- The centered physical condition retains both the average and endpoint
weighted-tail terms, with their exact signs. -/
theorem physicalPrimitive_centered_eq_tailAverage
    (f : ThresholdHilbert) (L : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K, hilbertSequence f (k + 1)) - (K : ℝ) * L =
      2 * (∑ k ∈ Finset.range K, (tailAverage f k - L)) -
        (K : ℝ) * (tailAverage f K - L) := by
  rw [physicalPrimitive_eq_tailAverage, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Centering the physical sequence subtracts exactly `K * L` from its primitive. -/
theorem physicalPrimitive_sub_const (f : ThresholdHilbert) (L : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K, hilbertSequence (f - L • hilbertOne) (k + 1)) =
      (∑ k ∈ Finset.range K, hilbertSequence f (k + 1)) - (K : ℝ) * L := by
  have hseq (k : ℕ) : hilbertSequence (f - L • hilbertOne) (k + 1) =
      hilbertSequence f (k + 1) - L := by
    change hilbertSequenceLinear (f - L • hilbertOne) (k + 1) = _
    rw [map_sub, map_smul]
    change hilbertSequence f (k + 1) - L * hilbertSequence hilbertOne (k + 1) = _
    rw [hilbertOne_sequence]
    simp [zeroAnchor]
  simp_rw [hseq]
  simp [Finset.sum_sub_distrib]

/-- The explicit variation weight only needs to control the centered primitive.
The removed constant mode has its own unconditional PNT pairing limit. -/
theorem rawMobiusResidual_inner_tendsto_of_summable_centered_primitive
    (f : ThresholdHilbert) (L : ℝ)
    (hH : Summable (fun K : ℕ =>
      |(∑ k ∈ Finset.range K, hilbertSequence f (k + 1)) - (K : ℝ) * L| *
        ((3 + ((K + 1).divisors.card : ℝ)) /
          (((K : ℝ) + 1) * ((K : ℝ) + 2))))) :
    Tendsto (fun N => inner ℝ (hilbertOne - rawMobiusHilbert N) f)
      atTop (𝓝 0) := by
  have hc := rawMobiusResidual_inner_tendsto_of_summable_primitive
    (f - L • hilbertOne) (by simpa only [physicalPrimitive_sub_const] using hH)
  have hL := rawMobiusResidual_inner_one_tendsto_zero.const_mul L
  simpa only [inner_sub_right, inner_smul_right, sub_add_cancel, mul_zero,
    add_zero] using hc.add hL

/-- A logarithmic bound on deviation from any linear primitive is enough. -/
theorem rawMobiusResidual_inner_tendsto_of_centered_primitive_log_bound
    (f : ThresholdHilbert) (L C p : ℝ) (hp : 2 < p)
    (hH : ∀ K : ℕ,
      |(∑ k ∈ Finset.range K, hilbertSequence f (k + 1)) - (K : ℝ) * L| ≤
        C * (((K : ℝ) + 1) / Real.log (2 * ((K : ℝ) + 1)) ^ p)) :
    Tendsto (fun N => inner ℝ (hilbertOne - rawMobiusHilbert N) f)
      atTop (𝓝 0) := by
  have hc := rawMobiusResidual_inner_tendsto_of_primitive_log_bound
    (f - L • hilbertOne) C p hp
    (by simpa only [physicalPrimitive_sub_const] using hH)
  have hL := rawMobiusResidual_inner_one_tendsto_zero.const_mul L
  simpa only [inner_sub_right, inner_smul_right, sub_add_cancel, mul_zero,
    add_zero] using hc.add hL

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The actual residual vanishes if a centered physical primitive is summable.
The summability assumption is an unproved arithmetic provider. -/
theorem limitResidual_eq_zero_of_summable_centered_primitive (L : ℝ)
    (hH : Summable (fun K : ℕ =>
      |(∑ k ∈ Finset.range K, hilbertSequence limitResidual (k + 1)) -
          (K : ℝ) * L| *
        ((3 + ((K + 1).divisors.card : ℝ)) /
          (((K : ℝ) + 1) * ((K : ℝ) + 2))))) :
    limitResidual = 0 := by
  have ht := rawMobiusResidual_inner_tendsto_of_summable_centered_primitive
    limitResidual L hH
  have hc : Tendsto (fun _ : ℕ => limitEnergy) atTop (𝓝 0) := by
    simpa only [rawMobiusResidual_inner_limitResidual] using ht
  exact limitResidual_zero_iff_energy_zero.mpr
    (tendsto_nhds_unique tendsto_const_nhds hc)

/-- Conditional RH reduction allowing an arbitrary asymptotic mean in the
physical primitive. No such mean or rate for the actual residual is asserted. -/
theorem riemannHypothesis_of_residual_centered_primitive_log_bound
    (L C p : ℝ) (hp : 2 < p)
    (hH : ∀ K : ℕ,
      |(∑ k ∈ Finset.range K, hilbertSequence limitResidual (k + 1)) -
          (K : ℝ) * L| ≤
        C * (((K : ℝ) + 1) / Real.log (2 * ((K : ℝ) + 1)) ^ p)) :
    RiemannHypothesis := by
  have ht := rawMobiusResidual_inner_tendsto_of_centered_primitive_log_bound
    limitResidual L C p hp hH
  have hc : Tendsto (fun _ : ℕ => limitEnergy) atTop (𝓝 0) := by
    simpa only [rawMobiusResidual_inner_limitResidual] using ht
  have he : limitEnergy = 0 := tendsto_nhds_unique tendsto_const_nhds hc
  apply riemannHypothesis_of_firstCoordinate_zero
  exact firstCoordinate_zero_iff_residual_zero.mpr
    (limitResidual_zero_iff_energy_zero.mpr he)

end RiemannResearch.RH.Pareto.CoefficientStabilization
