import RiemannResearch.RH.CanonicalMobiusWeightedEndpoint

/-!
# Exact discrete alpha-one cell energy

The endpoint cell weights are the exact integrals of x^(-3) on [n,n+1].
This module proves the discrete comparison and corrected-family convergence;
the continuous integral and Hardy-space identification are supplied separately.
No RH-critical norm convergence is asserted. Source: the endpoint comparison
in HardyEndpointCompactness20260924.md.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- Exact alpha-one cell weight, with the unused zeroth term zero. -/
def exactEndpointCellWeight (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) / (2 * (n : ℝ)^2 * ((n : ℝ) + 1)^2)

@[simp] theorem exactEndpointCellWeight_zero : exactEndpointCellWeight 0 = 0 := by
  norm_num [exactEndpointCellWeight]

theorem exactEndpointCellWeight_nonneg (n : ℕ) :
    0 ≤ exactEndpointCellWeight n := by
  unfold exactEndpointCellWeight
  positivity

/-- The rational weight is precisely half the difference of reciprocal squares. -/
theorem exactEndpointCellWeight_eq_sub (n : ℕ) (hn : 0 < n) :
    exactEndpointCellWeight n =
      (1 / (n : ℝ)^2 - 1 / ((n : ℝ) + 1)^2) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold exactEndpointCellWeight
  field_simp
  <;> ring

/-- Exact factor relating the cell norm to inverse-coordinate Pareto energy. -/
theorem exactEndpointCellWeight_factor (n : ℕ) :
    exactEndpointCellWeight n =
      (positiveWeight n / (n : ℝ)) *
        ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) := by
  by_cases hn : n = 0
  · subst n
    simp [exactEndpointCellWeight, positiveWeight]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    unfold exactEndpointCellWeight positiveWeight
    field_simp
    <;> ring

theorem exactEndpointCellWeight_le_inverseCoordinateWeight (n : ℕ) :
    exactEndpointCellWeight n ≤ positiveWeight n / (n : ℝ) := by
  have hfac : (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1)) ≤ 1 := by
    apply (div_le_one (show 0 < 2 * ((n : ℝ) + 1) by positivity)).mpr
    linarith
  rw [exactEndpointCellWeight_factor]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac
    (div_nonneg (positiveWeight_nonneg n) (Nat.cast_nonneg n))

/-- Full exact discrete alpha-one energy of a physical step vector. -/
def exactEndpointCellEnergy (x : ThresholdHilbert) : ℝ :=
  ∑' n : ℕ, exactEndpointCellWeight n * hilbertSequence x n ^ 2

/-- The inverse-coordinate energy series is summable for every Pareto vector. -/
theorem inverseCoordinateEnergy_summable (x : ThresholdHilbert) :
    Summable (fun n : ℕ => positiveWeight n * hilbertSequence x n ^ 2 / (n : ℝ)) := by
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
      (Nat.cast_nonneg n)) _ (hilbertSequence_square_summable x)
  intro n
  by_cases hn : n = 0
  · subst n
    simp [positiveWeight]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
    apply (div_le_iff₀ hn0).mpr
    nlinarith [mul_nonneg (positiveWeight_nonneg n) (sq_nonneg (hilbertSequence x n))]

/-- Exact cell-energy summability, with no tail removed. -/
theorem exactEndpointCellEnergy_summable (x : ThresholdHilbert) :
    Summable (fun n : ℕ => exactEndpointCellWeight n * hilbertSequence x n ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (exactEndpointCellWeight_nonneg n) (sq_nonneg _))
    _ (inverseCoordinateEnergy_summable x)
  intro n
  simpa only [div_mul_eq_mul_div] using
    mul_le_mul_of_nonneg_right (exactEndpointCellWeight_le_inverseCoordinateWeight n)
      (sq_nonneg (hilbertSequence x n))

theorem exactEndpointCellEnergy_nonneg (x : ThresholdHilbert) :
    0 ≤ exactEndpointCellEnergy x := by
  exact tsum_nonneg (fun n =>
    mul_nonneg (exactEndpointCellWeight_nonneg n) (sq_nonneg _))

theorem exactEndpointCellEnergy_le_inverseCoordinateEnergy (x : ThresholdHilbert) :
    exactEndpointCellEnergy x ≤ inverseCoordinateEnergy x := by
  apply (exactEndpointCellEnergy_summable x).tsum_le_tsum _
    (inverseCoordinateEnergy_summable x)
  intro n
  simpa only [div_mul_eq_mul_div] using
    mul_le_mul_of_nonneg_right (exactEndpointCellWeight_le_inverseCoordinateWeight n)
      (sq_nonneg (hilbertSequence x n))

/-- Unconditional corrected-family convergence in the exact alpha-one cell norm. -/
theorem canonicalMobiusResidual_exactEndpointCellEnergy_tendsto_zero :
    Tendsto (fun N => exactEndpointCellEnergy (hilbertOne - canonicalMobiusHilbert N))
      atTop (𝓝 0) := by
  exact squeeze_zero
    (fun N => exactEndpointCellEnergy_nonneg _)
    (fun N => exactEndpointCellEnergy_le_inverseCoordinateEnergy _)
    canonicalMobiusResidual_inverseCoordinateEnergy_tendsto_zero

end RiemannResearch.RH.Pareto
