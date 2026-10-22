import RiemannResearch.Analysis.DominatedPrimitivePairing
import RiemannResearch.NumberTheory.DivisorCountSummability
import RiemannResearch.RH.NaturalMobiusVariation

/-!
# Primitive tests of the actual raw Möbius residual

Source: the Abel argument in `ReciprocalCharge_DilationAndPeriodicSource_20260924.md`,
Section 7. This extension allows unbounded positive-coordinate partial sums.
The primitive must be absolutely summable against the explicit divisor-count
variation weight. Its endpoint condition follows from the elementary cutoff
bound for the actual raw Möbius residual. Bounded primitives and every fixed
sublinear-power primitive bound are included as corollaries.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto

/-- The actual pairing tends to zero if the primitive of the positive physical
    test coordinates is integrable against the divisor-count variation weight. -/
theorem rawMobiusResidual_inner_tendsto_of_summable_primitive
    (f : ThresholdHilbert)
    (hH : Summable (fun K : ℕ =>
      |∑ k ∈ Finset.range K, hilbertSequence f (k + 1)| *
        ((3 + ((K + 1).divisors.card : ℝ)) /
          (((K : ℝ) + 1) * ((K : ℝ) + 2))))) :
    Tendsto (fun N => inner ℝ (hilbertOne - rawMobiusHilbert N) f) atTop (𝓝 0) := by
  let h : ℕ → ℝ := fun k => hilbertSequence f (k + 1)
  let H : ℕ → ℝ := fun K => ∑ k ∈ Finset.range K, h k
  let F : ℕ → ℕ → ℝ := fun N k => rawMobiusWeightedCoordinate N (k + 1)
  let D : ℕ → ℝ := fun k => (3 + ((k + 1).divisors.card : ℝ)) /
    (((k : ℝ) + 1) * ((k : ℝ) + 2))
  have hH0 : H 0 = 0 := by simp [H]
  have hHstep : ∀ k, H (k + 1) = H k + h k := by
    intro k
    exact Finset.sum_range_succ _ _
  have hHD : Summable (fun k => |H k| * D k) := hH
  have hweight (k : ℕ) : positiveWeight (k + 1) ≤ D k := by
    dsimp [positiveWeight, D]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have ht : (0 : ℝ) ≤ ((k + 1).divisors.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hboundary : ∀ᶠ N in atTop,
      Tendsto (fun k => H k * F N k) atTop (𝓝 0) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hnorm (k : ℕ) : ‖H k * F N k‖ ≤ (N : ℝ) * (|H k| * D k) := by
      change |H k * (positiveWeight (k + 1) *
        hilbertSequence (hilbertOne - rawMobiusHilbert N) (k + 1))| ≤
          (N : ℝ) * (|H k| * D k)
      rw [abs_mul, abs_mul,
        abs_of_nonneg (positiveWeight_nonneg (k + 1))]
      calc
        _ ≤ |H k| * (positiveWeight (k + 1) * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (rawMobiusResidual_abs_le_cutoff N hN (k + 1))
              (positiveWeight_nonneg (k + 1))) (abs_nonneg _)
        _ ≤ |H k| * (D k * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hweight k) (Nat.cast_nonneg N)) (abs_nonneg _)
        _ = (N : ℝ) * (|H k| * D k) := by ring
    have hlim : Tendsto (fun k => (N : ℝ) * (|H k| * D k)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hHD.tendsto_atTop_zero.const_mul (N : ℝ)
    exact squeeze_zero_norm hnorm hlim
  have hpairs (N : ℕ) : Summable (fun k => h k * F N k) := by
    have hw := weighted_product_summable_of_square
      (hilbertSequence_square_summable (hilbertOne - rawMobiusHilbert N))
      (hilbertSequence_square_summable f)
    have hwshift := hw.comp_injective (fun a b (hab : a + 1 = b + 1) => by omega)
    apply hwshift.congr
    intro k
    dsimp [h, F, rawMobiusWeightedCoordinate]
    ring
  have hD : Summable (fun k => |H (k + 1)| * D (k + 1)) :=
    hHD.comp_injective (fun a b (hab : a + 1 = b + 1) => by omega)
  have hv : ∀ᶠ N in atTop, ∀ k, |F N k - F N (k + 1)| ≤ D (k + 1) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro k
    dsimp [F, D]
    rw [abs_sub_comm]
    simpa only [Nat.cast_add, Nat.cast_one] using
      rawMobiusWeightedCoordinate_variation_le N hN (k + 1) (by omega)
  have hp : ∀ k, Tendsto (fun N => F N k) atTop (𝓝 0) := by
    intro k
    simpa only [F, rawMobiusWeightedCoordinate, mul_zero] using
      (rawMobiusResidual_coordinate_tendsto_zero (k + 1)).const_mul (positiveWeight (k + 1))
  have ht := RiemannResearch.Analysis.dominatedPrimitive_pairing_tendsto_zero
    h H F (fun k => D (k + 1)) hH0 hHstep hboundary hpairs hD hv hp
  have he (N : ℕ) : (∑' k, h k * F N k) =
      inner ℝ (hilbertOne - rawMobiusHilbert N) f := by
    rw [hilbert_inner_weighted]
    unfold paretoInner
    have hw := weighted_product_summable_of_square
      (hilbertSequence_square_summable (hilbertOne - rawMobiusHilbert N))
      (hilbertSequence_square_summable f)
    rw [hw.tsum_eq_zero_add]
    simp only [hilbertSequence_zero, mul_zero, zero_add]
    apply tsum_congr
    intro k
    dsimp [h, F, rawMobiusWeightedCoordinate]
    ring
  simpa only [he] using ht

/-- Bounded positive-coordinate partial sums supply the weighted-primitive
    summability criterion, with no further arithmetic hypothesis. -/
theorem rawMobiusResidual_inner_tendsto_of_bounded_partial_sums
    (f : ThresholdHilbert) (B : ℝ)
    (hB : ∀ K, |∑ k ∈ Finset.range K, hilbertSequence f (k + 1)| ≤ B) :
    Tendsto (fun N => inner ℝ (hilbertOne - rawMobiusHilbert N) f) atTop (𝓝 0) := by
  apply rawMobiusResidual_inner_tendsto_of_summable_primitive f
  have hs :=
    RiemannResearch.NumberTheory.summable_divisor_count_successor_majorant.mul_left B
  apply hs.of_nonneg_of_le
  · intro K
    positivity
  · intro K
    exact mul_le_mul_of_nonneg_right (hB K) (by positivity)

/-- Any sublinear power bound for a fixed physical primitive supplies a test
    against which the raw Möbius residual tends to zero. -/
theorem rawMobiusResidual_inner_tendsto_of_primitive_rpow_bound
    (f : ThresholdHilbert) (C α : ℝ) (hα : α < 1)
    (hH : ∀ K : ℕ, |∑ k ∈ Finset.range K, hilbertSequence f (k + 1)| ≤
      C * ((K : ℝ) + 1) ^ α) :
    Tendsto (fun N => inner ℝ (hilbertOne - rawMobiusHilbert N) f) atTop (𝓝 0) := by
  apply rawMobiusResidual_inner_tendsto_of_summable_primitive f
  have hs :=
    (RiemannResearch.NumberTheory.summable_rpow_mul_divisor_count_successor_majorant
      α hα).mul_left C
  apply hs.of_nonneg_of_le
  · intro K
    positivity
  · intro K
    calc
      _ ≤ (C * ((K : ℝ) + 1) ^ α) *
          ((3 + ((K + 1).divisors.card : ℝ)) /
            (((K : ℝ) + 1) * ((K : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_right (hH K) (by positivity)
      _ = _ := by ring

end RiemannResearch.RH.Pareto
