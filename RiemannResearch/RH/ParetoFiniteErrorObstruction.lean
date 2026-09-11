import RiemannResearch.RH.ParetoLegalStructure
import RiemannResearch.RH.ThresholdLegalIntegrability
import RiemannResearch.RH.ParetoDefectContinuity
import RiemannResearch.RH.ParetoApproximationRatio

/-!
# Positive full error of every finite legal packet

Source: user-provided September 11, 2026 discussion of finite independence
versus completeness. A positive-coordinate zero has positive Pareto mass.
The resulting bound depends on the packet's common period; it is not a
uniform obstruction to sequences whose conductors grow.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A genuine positive-coordinate zero contributes its entire atom to error. -/
theorem positiveWeight_le_error_of_zero {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) {Q : ℕ} (hzero : f Q = 0) :
    positiveWeight Q ≤ paretoError f := by
  simpa only [hzero, sub_zero, one_pow, mul_one] using
    paretoError_coordinate_le hf Q

/-- Every finite legal packet has strictly positive full approximation error. -/
theorem legalSeedSpan_error_pos (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) : 0 < paretoError f := by
  obtain ⟨Q, hQ, hz⟩ := legalSeedSpan_exists_positive_zero A hA hf
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded A hA hf
  have hw : 0 < positiveWeight Q := by
    unfold positiveWeight
    have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
    positivity
  exact lt_of_lt_of_le hw (positiveWeight_le_error_of_zero hC hz)

/-- Mean-one finite legal packets cannot attain variance zero. -/
theorem legalSeedSpan_variance_pos (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) (hm : paretoMean f = 1) :
    0 < paretoVariance f := by
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded A hA hf
  have h := legalSeedSpan_error_pos A hA hf
  rw [paretoError_eq_variance_add_bias_sq hC, hm] at h
  simpa using h

/-- Integrated Ramanujan blocks vanish at every multiple of their conductor. -/
theorem ramanujanPacket_eq_zero_of_dvd {d Q : ℕ} (hd : d ∣ Q) :
    ramanujanPacket d Q = 0 := by
  unfold ramanujanPacket
  apply Finset.sum_eq_zero
  intro e he
  have heQ : e ∣ Q := dvd_trans (Nat.mem_divisors.mp he).1 hd
  simp [residue, Nat.mod_eq_zero_of_dvd heQ]

/-- A common multiple gives an explicit coefficient-independent finite-space
error floor, with no sign restriction on the coefficients. -/
theorem packetCombination_error_ge_common_multiple (s : Finset ℕ) (c : ℕ → ℝ)
    {Q : ℕ} (hQ : ∀ d ∈ s, d ∣ Q) :
    positiveWeight Q ≤ paretoError (fun n => ∑ d ∈ s, c d * ramanujanPacket d n) := by
  obtain ⟨C, hC⟩ := packetCombination_bounded s c
  apply positiveWeight_le_error_of_zero hC
  apply Finset.sum_eq_zero
  intro d hd
  rw [ramanujanPacket_eq_zero_of_dvd (hQ d hd), mul_zero]

/-- In particular, every fixed finite positive conductor set has a positive
error floor uniform over all its signed coefficients. -/
theorem packetCombination_fixed_support_error_floor (s : Finset ℕ)
    (hs : ∀ d ∈ s, 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℕ → ℝ,
      ε ≤ paretoError (fun n => ∑ d ∈ s, c d * ramanujanPacket d n) := by
  let Q : ℕ := ∏ d ∈ s, d
  have hQ : 0 < Q := Finset.prod_pos hs
  refine ⟨positiveWeight Q, ?_, ?_⟩
  · unfold positiveWeight
    have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
    positivity
  · intro c
    apply packetCombination_error_ge_common_multiple s c
    intro d hd
    exact Finset.dvd_prod_of_mem id hd

end
end RiemannResearch.RH.Pareto
