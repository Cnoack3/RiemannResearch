import RiemannResearch.RH.DyadicRegularizedNorm
import RiemannResearch.Analysis.FiniteGeometricDifference

/-!
# Exact finite arithmetic residue telescoping

Source: independently developed from the concrete arithmetic regularization
in user-provided DyadicAllScaleConvergenceVerification20260910(2).md.
The signed finite identity retains the entire terminal residue vector.
There is no passage from pointwise stabilization to Hilbert convergence.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The physical residue cocycle holds as an exact complete-H identity. -/
theorem hilbertDilation_residue_eq_sub (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    hilbertDilation n hn (hilbertResidue r hr) =
      hilbertResidue (n * r) (Nat.mul_pos hn hr) - hilbertResidue n hn := by
  apply hilbertSequence_injective
  funext k
  simp only [hilbertDilation_sequence, hilbertResidue_sequence, hilbertSequence_sub,
    Pi.sub_apply]
  exact residue_mul_floor n r k

/-- A complete finite triadic orbit equals signed residue differences.
The terminal is an actual Hilbert vector and has not been replaced by a
coordinatewise eventual value. -/
theorem triadicResidue_finite_weighted_telescope
    (q : ℝ) (n : ℕ) (hn : 0 < n) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), q ^ j •
      hilbertDilation (n * 3 ^ j) (by positivity)
        (hilbertResidue 3 (by norm_num))) =
      q ^ J • hilbertResidue (n * 3 ^ (J + 1)) (by positivity) -
        hilbertResidue n hn +
      (1 - q) • ∑ j ∈ Finset.range J, q ^ j •
        hilbertResidue (n * 3 ^ (j + 1)) (by positivity) := by
  have h := RiemannResearch.Analysis.finite_geometric_difference q
    (fun j => hilbertResidue (n * 3 ^ j) (by positivity)) J
  have hterm (j : ℕ) :
      hilbertDilation (n * 3 ^ j) (by positivity)
        (hilbertResidue 3 (by norm_num)) =
      hilbertResidue (n * 3 ^ (j + 1)) (by positivity) -
        hilbertResidue (n * 3 ^ j) (by positivity) := by
    simpa only [pow_succ, Nat.mul_assoc] using
      hilbertDilation_residue_eq_sub (n * 3 ^ j) 3 (by positivity) (by norm_num)
  simpa only [hterm, pow_zero, Nat.mul_one] using h

/-- The actual finite raw rectangle has this signed Abel decomposition,
including every Mobius coefficient and the full terminal residue column. -/
theorem dyadicRegularizedRawRectangle_residue_telescope
    (ε : ℝ) (M J : ℕ) :
    dyadicRegularizedRawRectangle ε M (J + 1) =
      dyadicRegularizationNormalization ε •
        ∑ m ∈ Finset.range M,
          ((ArithmeticFunction.moebius (m + 1) : ℝ) /
              (m + 1 : ℝ) ^ (1 + ε)) •
          (triadicDampingRatio ε ^ J •
              hilbertResidue ((m + 1) * 3 ^ (J + 1)) (by positivity) -
            hilbertResidue (m + 1) (by positivity) +
            (1 - triadicDampingRatio ε) •
              ∑ j ∈ Finset.range J, triadicDampingRatio ε ^ j •
                hilbertResidue ((m + 1) * 3 ^ (j + 1)) (by positivity)) := by
  unfold dyadicRegularizedRawRectangle
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [← triadicResidue_finite_weighted_telescope
    (triadicDampingRatio ε) (m + 1) (by positivity) J]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [dyadicRegularizationCoefficient, smul_smul]

/-- The exact same signed identity after the genuine quotient projection. -/
theorem dyadicRegularizedRectangle_residue_telescope
    (ε : ℝ) (M J : ℕ) :
    dyadicRegularizedRectangle ε M (J + 1) =
      dyadicRegularizationNormalization ε •
        ∑ m ∈ Finset.range M,
          ((ArithmeticFunction.moebius (m + 1) : ℝ) /
              (m + 1 : ℝ) ^ (1 + ε)) •
          (triadicDampingRatio ε ^ J •
              dyadicQuotientProjection
                (hilbertResidue ((m + 1) * 3 ^ (J + 1)) (by positivity)) -
            dyadicQuotientProjection (hilbertResidue (m + 1) (by positivity)) +
            (1 - triadicDampingRatio ε) •
              ∑ j ∈ Finset.range J, triadicDampingRatio ε ^ j •
                dyadicQuotientProjection
                  (hilbertResidue ((m + 1) * 3 ^ (j + 1)) (by positivity))) := by
  rw [dyadicRegularizedRectangle,
    dyadicRegularizedRawRectangle_residue_telescope]
  simp only [map_smul, map_sum, map_add, map_sub]

end
end RiemannResearch.RH.Pareto
