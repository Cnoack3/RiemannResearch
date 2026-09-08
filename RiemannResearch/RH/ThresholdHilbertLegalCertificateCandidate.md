# ThresholdHilbertLegalCertificate — unverified candidate

**Not verified by Lean.** No theorem in this candidate is claimed proved. See [attempt report](ThresholdOperatorComparisonAttempt.md).

```lean
import RiemannResearch.RH.ThresholdHilbertFiniteLegal
import RiemannResearch.RH.ThresholdInfiniteCertificate

/-!
# Concrete period-36 bounds for the actual legal projections

Source: Christian Noack's RH_Two_Seed_Threshold.tex, Section 10; the existing
ThresholdInfiniteCertificate proves the rational full-tail witness bound.
This module identifies its actual weighted-H vector and places it in the
explicit finite two-seed space with scales {1,2,3,6,9,18}. It then transfers
the numerical certificate to the genuine finite and closed legal projections.
No density, optimality formula, or RH hypothesis is used.
-/

namespace RiemannResearch.RH.Pareto
open TwoSeedThreshold
noncomputable section

/-- Six actual positive integer scales sufficient for the eight-term witness. -/
def legalWitness36Scales : Finset ℕ+ := {1, 2, 3, 6, 9, 18}

/-- The full-tail weighted-H realization of the previously certified witness. -/
def hilbertLegalWitness36 : ThresholdHilbert :=
  (1 / 1000 : ℝ) •
    ((556 : ℝ) • hilbertResidueDilation 2 1 +
     (117 : ℝ) • hilbertResidueDilation 2 2 +
      (18 : ℝ) • hilbertResidueDilation 2 3 +
       (6 : ℝ) • hilbertResidueDilation 2 6 +
       (7 : ℝ) • hilbertResidueDilation 2 9 +
       (2 : ℝ) • hilbertResidueDilation 2 18 +
     (367 : ℝ) • hilbertResidueDilation 3 1 +
      (50 : ℝ) • hilbertResidueDilation 3 3)

theorem hilbertLegalWitness36_sequence :
    hilbertSequence hilbertLegalWitness36 = legalWitness36 := by
  funext k
  simp only [hilbertLegalWitness36, hilbertSequence_smul, hilbertSequence_add,
    hilbertResidueDilation_sequence, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    legalWitness36, certificateGenerator_eq_dilation, PNat.val_ofNat]
  ring

theorem hilbertLegalWitness36_mem_finite :
    hilbertLegalWitness36 ∈ finiteTwoSeedSpan legalWitness36Scales := by
  let L := finiteTwoSeedSpan legalWitness36Scales
  change hilbertLegalWitness36 ∈ L
  unfold hilbertLegalWitness36
  apply L.smul_mem
  repeat' apply L.add_mem
  all_goals apply L.smul_mem
  all_goals first
    | exact hilbertResidueDilation_two_mem _ (by norm_num [legalWitness36Scales])
    | exact hilbertResidueDilation_three_mem _ (by norm_num [legalWitness36Scales])

/-- Exact identification with the certified infinite positive-index error. -/
theorem hilbertLegalWitness36_error_eq :
    ‖hilbertOne - hilbertLegalWitness36‖^2 =
      ∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness36 (k+1))^2 := by
  have hsub : hilbertSequence (hilbertOne - hilbertLegalWitness36) =
      hilbertSequence hilbertOne - hilbertSequence hilbertLegalWitness36 :=
    hilbertSequenceLinear.map_sub _ _
  rw [hilbert_norm_weighted_sq,
    (hilbertSequence_square_summable (hilbertOne - hilbertLegalWitness36)).tsum_eq_zero_add]
  simp only [hilbertSequence_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
  apply tsum_congr
  intro k
  rw [hsub, hilbertOne_sequence, hilbertLegalWitness36_sequence]
  simp [zeroAnchor]

theorem hilbertLegalWitness36_error_lt :
    ‖hilbertOne - hilbertLegalWitness36‖^2 < (53 : ℝ) / 1000 := by
  rw [hilbertLegalWitness36_error_eq]
  exact legalWitness36_full_error_lt

/-- The actual finite optimal legal fit at these six scales beats the complete-tail threshold. -/
theorem finiteTwoSeedProjection_period36_error_lt :
    ‖hilbertOne - finiteTwoSeedProjection legalWitness36Scales hilbertOne‖^2 <
      (53 : ℝ) / 1000 := by
  have h := finiteTwoSeedProjection_best_approximation legalWitness36Scales
    hilbertOne hilbertLegalWitness36 hilbertLegalWitness36_mem_finite
  nlinarith [hilbertLegalWitness36_error_lt,
    sq_nonneg ‖finiteTwoSeedProjection legalWitness36Scales hilbertOne - hilbertLegalWitness36‖]

/-- More than 94.7 percent of the unit target energy is captured by the actual finite legal projection. -/
theorem finiteTwoSeedProjection_period36_energy_gt :
    (947 : ℝ) / 1000 < ‖finiteTwoSeedProjection legalWitness36Scales hilbertOne‖^2 := by
  linarith [finiteTwoSeedProjection_target_error legalWitness36Scales,
    finiteTwoSeedProjection_period36_error_lt]

theorem hilbertLegalWitness36_mem_closure :
    hilbertLegalWitness36 ∈ hilbertLegalClosure ({2, 3} : Set ℕ) :=
  (Submodule.le_topologicalClosure _)
    (finiteTwoSeedSpan_le_legal _ hilbertLegalWitness36_mem_finite)

/-- The true closed legal projection satisfies the same strict full-tail certificate. -/
theorem twoSeedLegalProjection_period36_error_lt :
    ‖hilbertOne - twoSeedLegalProjection hilbertOne‖^2 < (53 : ℝ) / 1000 := by
  let K := hilbertLegalClosure ({2, 3} : Set ℕ)
  have hw : K.starProjection hilbertLegalWitness36 = hilbertLegalWitness36 :=
    Submodule.starProjection_eq_self_iff.mpr hilbertLegalWitness36_mem_closure
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection
    (hilbertOne - hilbertLegalWitness36) K
  rw [Submodule.starProjection_orthogonal_val] at h
  simp only [map_sub, hw] at h
  have he : hilbertOne - hilbertLegalWitness36 -
      (K.starProjection hilbertOne - hilbertLegalWitness36) =
        hilbertOne - K.starProjection hilbertOne := by abel
  rw [he] at h
  change ‖hilbertOne - K.starProjection hilbertOne‖^2 < (53 : ℝ) / 1000
  nlinarith [hilbertLegalWitness36_error_lt,
    sq_nonneg ‖K.starProjection hilbertOne - hilbertLegalWitness36‖]

/-- Concrete unconditional captured energy of the actual full legal projection. -/
theorem twoSeedLegalProjection_period36_energy_gt :
    (947 : ℝ) / 1000 < ‖twoSeedLegalProjection hilbertOne‖^2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection hilbertOne
    (hilbertLegalClosure ({2, 3} : Set ℕ))
  rw [hilbertOne_norm_sq, Submodule.starProjection_orthogonal_val] at h
  change 1 = ‖twoSeedLegalProjection hilbertOne‖^2 +
    ‖hilbertOne - twoSeedLegalProjection hilbertOne‖^2 at h
  linarith [twoSeedLegalProjection_period36_error_lt]

end
end RiemannResearch.RH.Pareto
```
