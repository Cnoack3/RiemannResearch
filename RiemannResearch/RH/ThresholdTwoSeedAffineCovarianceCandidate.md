# ThresholdTwoSeedAffineCovariance — unverified candidate

**Not verified by Lean.** No theorem in this candidate is claimed proved. See [attempt report](ThresholdOperatorComparisonAttempt.md).

```lean
import RiemannResearch.RH.ThresholdHilbertFiniteLegal
import RiemannResearch.RH.ThresholdAffineOperatorComparison

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Exact comparison of actual legal covariance. Both mixed terms are retained. -/
theorem twoSeedBlockCovariance_uniform_comparison (m : ℕ) (hm : 0 < m)
    (M : Finset ℕ+) (f g : ThresholdHilbert) :
    inner ℝ (twoSeedBlockCovariance m hm M f) g =
      inner ℝ
        (finiteTwoSeedProjection M (hilbertUniformBlockProjection m hm f))
        (finiteTwoSeedProjection M (hilbertUniformBlockProjection m hm g)) +
      inner ℝ
        (finiteTwoSeedProjection M (hilbertAffineDiscrepancy m hm f))
        (finiteTwoSeedProjection M (hilbertAffineDiscrepancy m hm g)) +
      inner ℝ
        (finiteTwoSeedProjection M (hilbertUniformBlockProjection m hm f))
        (finiteTwoSeedProjection M (hilbertAffineDiscrepancy m hm g)) +
      inner ℝ
        (finiteTwoSeedProjection M (hilbertAffineDiscrepancy m hm f))
        (finiteTwoSeedProjection M (hilbertUniformBlockProjection m hm g)) := by
  rw [twoSeedBlockCovariance_inner]
  have hf : hilbertAffineDiscrepancy m hm f =
      hilbertBlockProjection m hm f - hilbertUniformBlockProjection m hm f := rfl
  have hg : hilbertAffineDiscrepancy m hm g =
      hilbertBlockProjection m hm g - hilbertUniformBlockProjection m hm g := rfl
  rw [hf, hg, map_sub, map_sub]
  simp only [inner_sub_left, inner_sub_right]
  ring

/-- The actual scalar correction includes the signed mixed covariance. -/
theorem twoSeedBlockCovariance_uniform_energy (m : ℕ) (hm : 0 < m)
    (M : Finset ℕ+) (f : ThresholdHilbert) :
    inner ℝ (twoSeedBlockCovariance m hm M f) f =
      ‖finiteTwoSeedProjection M (hilbertUniformBlockProjection m hm f)‖^2 +
      ‖finiteTwoSeedProjection M (hilbertAffineDiscrepancy m hm f)‖^2 +
      2 * inner ℝ
        (finiteTwoSeedProjection M (hilbertUniformBlockProjection m hm f))
        (finiteTwoSeedProjection M (hilbertAffineDiscrepancy m hm f)) := by
  rw [twoSeedBlockCovariance_uniform_comparison,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h := real_inner_comm
    (finiteTwoSeedProjection M (hilbertUniformBlockProjection m hm f))
    (finiteTwoSeedProjection M (hilbertAffineDiscrepancy m hm f))
  linarith

end
end RiemannResearch.RH.Pareto
```
