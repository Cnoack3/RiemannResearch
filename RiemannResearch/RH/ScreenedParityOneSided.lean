import RiemannResearch.RH.ParetoAnnihilatorOneSided
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MeanOneResidualFloor
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.Linarith

/-!
# One-sided bounds for the normalized screened parity packet

The constant residual is orthogonal to every legal residue. Its physical
values are an affine function of the normalized screened parity packet.
A uniform bound on either side therefore forces its mean, and hence its
squared norm, to vanish.

Source: Christian Noack's question about identifying the screened direction
with the constant and the Pareto absolute-tail argument.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- Physical affine relation between the legal residual and the screened direction. -/
theorem limitResidual_at_pos_eq_screenedTwo (k : ℕ) (hk : 0 < k) :
    hilbertSequence limitResidual k =
      1 - (1 - limitEnergy) * hilbertSequence normalizedScreenedTwo k := by
  rw [limitResidual, limitProjection_eq_scaled_screenedTwo, ← anchoredEvaluationCLM_apply,
    map_sub, map_smul, smul_eq_mul, anchoredEvaluationCLM_apply, anchoredEvaluationCLM_apply,
    hilbertOne_sequence]
  simp [zeroAnchor, hk.ne']

/-- Either an upper or a lower uniform bound on positive sites identifies the screened packet. -/
theorem normalizedScreenedTwo_eq_one_of_oneSidedBound
    (hbound : (∃ C : ℝ, ∀ k : ℕ, 0 < k → C ≤ hilbertSequence normalizedScreenedTwo k) ∨
      (∃ C : ℝ, ∀ k : ℕ, 0 < k → hilbertSequence normalizedScreenedTwo k ≤ C)) :
    normalizedScreenedTwo = hilbertOne := by
  have hcoef : 0 ≤ 1 - limitEnergy := limitProjection_norm_sq ▸ sq_nonneg _
  have he : inner ℝ limitResidual hilbertOne = 0 := by
    rcases hbound with ⟨C, hC⟩ | ⟨C, hC⟩
    · apply annihilator_mean_zero_of_upper_bound _ limitResidual_mem_orthogonal
      refine ⟨1 - (1 - limitEnergy) * C, fun k hk => ?_⟩
      rw [limitResidual_at_pos_eq_screenedTwo k hk]
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left (hC k hk) hcoef) _
    · have hb : ∃ B : ℝ, ∀ k : ℕ, 0 < k → hilbertSequence (-limitResidual) k ≤ B := by
        refine ⟨(1 - limitEnergy) * C - 1, fun k hk => ?_⟩
        rw [← anchoredEvaluationCLM_apply, map_neg, anchoredEvaluationCLM_apply,
          limitResidual_at_pos_eq_screenedTwo k hk]
        linarith [mul_le_mul_of_nonneg_left (hC k hk) hcoef]
      have h := annihilator_mean_zero_of_upper_bound _ (closedSpace.orthogonal.neg_mem limitResidual_mem_orthogonal) hb
      simpa only [inner_neg_left, neg_eq_zero] using h
  have hE : limitEnergy = 0 := limitResidual_inner_one.symm.trans he
  have herr := normalizedScreenedTwo_error_sq_eq_limitEnergy
  rw [hE, zero_div, pow_two, mul_eq_zero, or_self, norm_eq_zero, sub_eq_zero] at herr
  exact herr

/-- Every nonconstant screened parity packet would have arbitrarily large
positive and negative physical values. -/
theorem screenedTwo_unbounded_both_sides_of_ne_one (hne : normalizedScreenedTwo ≠ hilbertOne)
    (B : ℝ) :
    (∃ k : ℕ, 0 < k ∧ B < hilbertSequence normalizedScreenedTwo k) ∧
    (∃ k : ℕ, 0 < k ∧ hilbertSequence normalizedScreenedTwo k < -B) := by
  constructor
  · by_contra h
    push Not at h
    exact hne (normalizedScreenedTwo_eq_one_of_oneSidedBound (Or.inr ⟨B, h⟩))
  · by_contra h
    push Not at h
    exact hne (normalizedScreenedTwo_eq_one_of_oneSidedBound (Or.inl ⟨-B, h⟩))

end RiemannResearch.RH.Pareto.PrimePowerSchur
