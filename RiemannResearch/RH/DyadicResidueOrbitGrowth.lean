import RiemannResearch.RH.DyadicArithmeticResidueTelescoping
import RiemannResearch.RH.DyadicResidueDepthGrowth

/-!
# Projected terminal residue growth along a triadic orbit

Source: independently developed from the exact finite residue telescope and
the proved all-scale dyadic depth bound. The first theorem is exact; the
second controls the actual projected terminal quadratically in depth.
No uniform estimate over the signed Mobius family is inferred.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem dyadicQuotientProjection_residue_triadic_reconstruction
    (n : ℕ) (hn : 0 < n) (J : ℕ) :
    dyadicQuotientProjection
        (hilbertResidue (n * 3 ^ (J + 1)) (by positivity)) =
      dyadicQuotientProjection (hilbertResidue n hn) +
        ∑ j ∈ Finset.range (J + 1),
          dyadicQuotientProjection
            (hilbertDilation (n * 3 ^ j) (by positivity)
              (hilbertResidue 3 (by norm_num))) := by
  have h := congrArg dyadicQuotientProjection
    (triadicResidue_finite_weighted_telescope 1 n hn J)
  simp only [one_pow, one_smul, sub_self, zero_smul, add_zero,
    map_sum, map_sub] at h
  rw [h]
  abel

/-- The genuine terminal residue has a quadratic-in-depth quotient bound. -/
theorem dyadicQuotientProjection_residue_triadic_norm_le_quadratic
    (n L J : ℕ) (hn : 0 < n) (hnL : n ≤ 2 ^ L) :
    ‖dyadicQuotientProjection
      (hilbertResidue (n * 3 ^ (J + 1)) (by positivity))‖ ≤
      ‖dyadicQuotientProjection (hilbertResidue n hn)‖ +
        ((J + 1 : ℕ) : ℝ) *
          (4 * ((L + 2 * J : ℕ) : ℝ) / Real.sqrt 2 +
            ‖hilbertResidue 3 (by norm_num)‖) := by
  rw [dyadicQuotientProjection_residue_triadic_reconstruction n hn J]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1),
        (4 * ((L + 2 * J : ℕ) : ℝ) / Real.sqrt 2 +
          ‖hilbertResidue 3 (by norm_num)‖) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j ≤ J := by have := Finset.mem_range.mp hj; omega
      have hthree : (3 : ℕ) ^ j ≤ 2 ^ (2 * j) := by
        calc
          3 ^ j ≤ 4 ^ j := pow_le_pow_left' (by norm_num : (3 : ℕ) ≤ 4) j
          _ = (2 ^ 2) ^ j := by norm_num
          _ = 2 ^ (2 * j) := (pow_mul 2 2 j).symm
      have hscale : n * 3 ^ j ≤ 2 ^ (L + 2 * J) := by
        calc
          _ ≤ 2 ^ L * 2 ^ (2 * j) := Nat.mul_le_mul hnL hthree
          _ = 2 ^ (L + 2 * j) := (pow_add 2 L (2 * j)).symm
          _ ≤ 2 ^ (L + 2 * J) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact dyadicQuotientProjection_triadicResidue_norm_le_depth
        (L + 2 * J) (n * 3 ^ j) (by positivity) hscale
    _ = _ := by simp <;> ring

end
end RiemannResearch.RH.Pareto
