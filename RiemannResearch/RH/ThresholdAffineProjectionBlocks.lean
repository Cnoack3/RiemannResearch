import RiemannResearch.RH.ThresholdAffineBranches
import RiemannResearch.LinearAlgebra.RankOneProjectionDistance

/-!
# Exact affine projection discrepancy on each finite physical block

Source: user-provided `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Section 11.2. We assemble the actual Pareto branch coefficients and the
finite rank-one identity. The infinite sum and its limiting phase constant
remain outside this module.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto

theorem uniformBranchCoefficient_product (m : ℕ) :
    (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt m) = 1 / (m : ℝ) := by
  rw [← pow_two, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg m)]

theorem uniformBranchCoefficient_sq_sum (m : ℕ) (hm : 0 < m) :
    (∑ r ∈ Finset.range m, (1 / Real.sqrt (m : ℝ)) ^ 2) = 1 := by
  have hu : (1 / Real.sqrt (m : ℝ)) ^ 2 = 1 / (m : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  simp only [hu, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact squared Hilbert--Schmidt discrepancy on the block over source `j`,
expressed entirely in the actual normalized Pareto branch coefficients. -/
theorem affineProjection_block_discrepancy (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (∑ r ∈ Finset.range m, ∑ t ∈ Finset.range m,
      (affineBranchCoefficient m r j * affineBranchCoefficient m t j -
        1 / (m : ℝ)) ^ 2) =
      2 * (1 - ((1 / Real.sqrt m) *
        (∑ r ∈ Finset.range m, affineBranchCoefficient m r j)) ^ 2) := by
  have h := Real.unit_rankOne_difference_sum_sq (Finset.range m)
    (fun r => affineBranchCoefficient m r j) (fun _ => 1 / Real.sqrt (m : ℝ))
    (affineBranchCoefficient_sq_sum m j hm hj) (uniformBranchCoefficient_sq_sum m hm)
  simp only [uniformBranchCoefficient_product, ← Finset.sum_mul] at h
  calc
    _ = 2 * (1 - ((∑ r ∈ Finset.range m, affineBranchCoefficient m r j) *
        (1 / Real.sqrt m)) ^ 2) := h
    _ = _ := by ring

end RiemannResearch.RH.Pareto
