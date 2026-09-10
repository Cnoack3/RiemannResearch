import RiemannResearch.RH.DyadicRegularizedBoundaryCoefficients
import RiemannResearch.RH.DyadicAdjointCoordinates
import RiemannResearch.RH.DyadicKernelJumpEnergy

/-!
# Exact weighted residue blocks underlying every signed boundary coefficient

Source: user-provided DyadicSignedMeanEnergyVerification20260910(1).md,
September 10, 2026, next bounded target. The complete physical resolvent and
its exact weighted blocks identify the residue boundary coordinate with an
absolutely convergent dyadic block series. Both neighboring blocks and every
arithmetic residue are retained. No uniform arithmetic square-sum estimate
is inferred from fixed-conductor absolute convergence.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.Analysis.AbelCoboundary
noncomputable section

/-- The exact physical coordinate of the complete resolvent controls the
boundary coefficient; its dyadic jump retains both adjacent values. -/
theorem dyadicBoundaryCoordinate_eq_resolvent_pairing
    (f : ThresholdHilbert) (i : ℕ) :
    dyadicBoundaryCoordinate f i =
      2 * inner ℝ (dyadicStepBoundary (i+1) (by positivity))
        (dyadicCriticalResolvent f) := by
  rw [← dyadicBoundaryCoordinate_projection f i,
    ← dyadicQuotientProjection_kernelDefect_resolvent f]
  unfold dyadicBoundaryCoordinate dyadicBoundaryVector
  rw [← dyadicQuotientProjection_inner, dyadicQuotientProjection_idempotent,
    dyadicProjectedBoundary_inner_kernelDefect]
  ring

theorem dyadicBoundaryCoordinate_eq_resolvent_jump
    (f : ThresholdHilbert) (i : ℕ) :
    dyadicBoundaryCoordinate f i =
      (hilbertSequence (dyadicCriticalResolvent f) (2*(i+1)+1) -
        hilbertSequence (dyadicCriticalResolvent f) (2*(i+1))) /
        (2*((i : ℝ)+1)+1) := by
  rw [dyadicBoundaryCoordinate_eq_resolvent_pairing,
    dyadicStepBoundary_inner_coordinates]
  push_cast
  field_simp

theorem dyadicBoundaryCoordinate_eq_halfAdjoint_series
    (f : ThresholdHilbert) (i : ℕ) :
    dyadicBoundaryCoordinate f i =
      ∑' j : ℕ, 2 * inner ℝ (dyadicStepBoundary (i+1) (by positivity))
        (orbit dyadicHalfAdjoint f j) := by
  rw [dyadicBoundaryCoordinate_eq_resolvent_pairing, dyadicCriticalResolvent]
  have he :
      inner ℝ (dyadicStepBoundary (i+1) (by positivity))
        (∑' j : ℕ, orbit dyadicHalfAdjoint f j) =
      ∑' j : ℕ, inner ℝ (dyadicStepBoundary (i+1) (by positivity))
        (orbit dyadicHalfAdjoint f j) :=
    (innerSL ℝ (dyadicStepBoundary (i+1) (by positivity))).map_tsum
      (dyadicCriticalResolvent_summable f)
  rw [he, tsum_mul_left]

/-- A dyadic level is the exact signed difference of its two physical blocks. -/
theorem dyadicHalfAdjoint_boundary_pairing_eq_blocks
    (f : ThresholdHilbert) (i j : ℕ) :
    2 * inner ℝ (dyadicStepBoundary (i+1) (by positivity))
      (orbit dyadicHalfAdjoint f j) =
      (2*((i : ℝ)+1)+2) *
        (∑ n ∈ Finset.Ico (2^j*(2*(i+1)+1)) (2^j*(2*(i+1)+2)),
          positiveWeight n * hilbertSequence f n) -
      (2*((i : ℝ)+1)) *
        (∑ n ∈ Finset.Ico (2^j*(2*(i+1))) (2^j*(2*(i+1)+1)),
          positiveWeight n * hilbertSequence f n) := by
  rw [dyadicStepBoundary_inner_coordinates,
    dyadicHalfAdjoint_orbit_coordinate _ _ _ (by positivity),
    dyadicHalfAdjoint_orbit_coordinate _ _ _ (by positivity)]
  simp only [Nat.add_assoc]
  unfold positiveWeight
  push_cast
  field_simp
  ring

/-- The actual two-block residue difference at scale `2^j`. -/
def dyadicResidueBoundaryBlock (a i j : ℕ) : ℝ :=
  (2*((i : ℝ)+1)+2) *
    (∑ n ∈ Finset.Ico (2^j*(2*(i+1)+1)) (2^j*(2*(i+1)+2)),
      positiveWeight n * residue a n) -
  (2*((i : ℝ)+1)) *
    (∑ n ∈ Finset.Ico (2^j*(2*(i+1))) (2^j*(2*(i+1)+1)),
      positiveWeight n * residue a n)

theorem dyadicResidueBoundaryBlock_eq_pairing
    (a i j : ℕ) (ha : 0 < a) :
    dyadicResidueBoundaryBlock a i j =
      2 * inner ℝ (dyadicStepBoundary (i+1) (by positivity))
        (orbit dyadicHalfAdjoint (hilbertResidue a ha) j) := by
  simpa only [dyadicResidueBoundaryBlock, hilbertResidue_sequence] using
    (dyadicHalfAdjoint_boundary_pairing_eq_blocks (hilbertResidue a ha) i j).symm

/-- The abstract projected residue coefficient now has a fully explicit
arithmetic formula in actual weights and residues at every dyadic scale. -/
theorem dyadicBoundaryCoordinate_residue_eq_blocks
    (a i : ℕ) (ha : 0 < a) :
    dyadicBoundaryCoordinate (hilbertResidue a ha) i =
      ∑' j : ℕ, dyadicResidueBoundaryBlock a i j := by
  rw [dyadicBoundaryCoordinate_eq_halfAdjoint_series]
  apply tsum_congr
  intro j
  exact (dyadicResidueBoundaryBlock_eq_pairing a i j ha).symm

theorem dyadicResidueBoundaryBlock_abs_summable
    (a i : ℕ) (ha : 0 < a) :
    Summable (fun j : ℕ => |dyadicResidueBoundaryBlock a i j|) := by
  let b := dyadicStepBoundary (i+1) (by positivity)
  let f := hilbertResidue a ha
  have hg := (summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (3/4 : ℝ) < 1)).mul_right
      (2 * ‖b‖ * ‖f‖)
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ hg
  intro j
  rw [dyadicResidueBoundaryBlock_eq_pairing a i j ha,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hi : |inner ℝ b (orbit dyadicHalfAdjoint f j)| ≤
      ‖b‖ * ‖orbit dyadicHalfAdjoint f j‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_inner_le_norm (𝕜 := ℝ) b (orbit dyadicHalfAdjoint f j)
  have ho := dyadicHalfAdjoint_orbit_norm_le f j
  calc
    _ ≤ 2 * (‖b‖ * ‖orbit dyadicHalfAdjoint f j‖) := by
      change 2 * |inner ℝ b (orbit dyadicHalfAdjoint f j)| ≤ _
      exact mul_le_mul_of_nonneg_left hi (by norm_num)
    _ ≤ 2 * (‖b‖ * ((3/4 : ℝ)^j * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ho (norm_nonneg b)) (by norm_num)
    _ = _ := by ring

/-- The exact signed arithmetic coefficient written entirely as nested
weighted residue-block sums. Fixed positive damping justifies the outer sum;
no rearrangement into a single unrestricted triple sum is made. -/
theorem dyadicSignedBoundaryCoefficient_eq_residue_blocks
    (ε : ℝ) (i : ℕ) :
    dyadicSignedBoundaryCoefficient ε i =
      dyadicRegularizationNormalization ε *
        ∑' p : ℕ × ℕ,
          ((ArithmeticFunction.moebius (p.1 + 1) : ℝ) /
            (p.1 + 1 : ℝ) ^ (1 + ε) * triadicDampingRatio ε ^ p.2) *
          ((∑' j : ℕ,
            dyadicResidueBoundaryBlock ((p.1 + 1) * 3 ^ (p.2 + 1)) i j) -
           (∑' j : ℕ,
            dyadicResidueBoundaryBlock ((p.1 + 1) * 3 ^ p.2) i j)) := by
  unfold dyadicSignedBoundaryCoefficient
  congr 1
  apply tsum_congr
  intro p
  rw [dyadicBoundaryCoordinate_residue_eq_blocks,
    dyadicBoundaryCoordinate_residue_eq_blocks]

end
end RiemannResearch.RH.Pareto
