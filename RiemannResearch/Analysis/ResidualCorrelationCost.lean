import RiemannResearch.Analysis.CorrelationNormalizedCorrection
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact residual-normalized correction cost

Source: the user-provided categorical CRT and energy note (14 November 2026),
equation F and its logarithmic-cost application. The cost uses the actual
residual and admissible subspace. All results are exact Hilbert-space facts;
the arithmetic logarithmic projection lower bound remains a separate input.
-/

noncomputable section
open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace RiemannResearch.Analysis.CorrelationCorrection
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (W : Submodule ℝ H) [W.HasOrthogonalProjection] (r : H)

theorem projected_correlation (w : H) (hw : w ∈ W) :
    inner ℝ r w = inner ℝ (W.starProjection r) w := by
  have h := Submodule.starProjection_inner_eq_zero r w hw
  rw [inner_sub_left] at h
  linarith

theorem projected_self_correlation :
    inner ℝ r (W.starProjection r) = ‖W.starProjection r‖ ^ 2 := by
  rw [projected_correlation W r _ (W.starProjection_apply_mem r),
    real_inner_self_eq_norm_sq]

theorem projection_zero_infeasible (hp : W.starProjection r = 0) :
    ¬ ∃ w ∈ W, inner ℝ r w ≠ 0 := by
  rintro ⟨w, hw, hc⟩
  apply hc
  rw [projected_correlation W r w hw, hp, inner_zero_left]

theorem residual_ratio_lower (hp : W.starProjection r ≠ 0)
    (w : H) (hw : w ∈ W) (hc : inner ℝ r w ≠ 0) :
    1 / ‖W.starProjection r‖ ^ 2 ≤ ‖w‖ ^ 2 / (inner ℝ r w) ^ 2 := by
  have hpos : 0 < ‖W.starProjection r‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hp)
  have hcpos : 0 < (inner ℝ r w) ^ 2 := sq_pos_of_ne_zero hc
  apply (div_le_div_iff₀ hpos hcpos).mpr
  have h := inner_sq_le (W.starProjection r) w
  rw [← projected_correlation W r w hw] at h
  simpa only [one_mul, mul_one, mul_comm] using h

theorem residual_ratio_attained (hp : W.starProjection r ≠ 0) :
    ‖W.starProjection r‖ ^ 2 / (inner ℝ r (W.starProjection r)) ^ 2 =
      1 / ‖W.starProjection r‖ ^ 2 := by
  rw [projected_self_correlation]
  have hn : ‖W.starProjection r‖ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hp))
  field_simp

/-- Infimum over actual nonzero residual correlations. Empty admissible sets
have cost top, so orthogonal residuals are never assigned zero cost. -/
def residualCorrelationCost : ℝ≥0∞ :=
  ⨅ w : H, ⨅ (_ : w ∈ W), ⨅ (_ : inner ℝ r w ≠ 0),
    ENNReal.ofReal (‖w‖ ^ 2 / (inner ℝ r w) ^ 2)

theorem residualCorrelationCost_zero (hp : W.starProjection r = 0) :
    residualCorrelationCost W r = ⊤ := by
  apply top_unique
  apply le_iInf
  intro w
  apply le_iInf
  intro hw
  apply le_iInf
  intro hc
  exact False.elim (projection_zero_infeasible W r hp ⟨w, hw, hc⟩)

theorem residualCorrelationCost_nonzero (hp : W.starProjection r ≠ 0) :
    residualCorrelationCost W r = ENNReal.ofReal (1 / ‖W.starProjection r‖ ^ 2) := by
  apply le_antisymm
  · apply iInf_le_of_le (W.starProjection r)
    apply iInf_le_of_le (W.starProjection_apply_mem r)
    have hc : inner ℝ r (W.starProjection r) ≠ 0 := by
      rw [projected_self_correlation]
      exact ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hp))
    apply iInf_le_of_le hc
    rw [residual_ratio_attained W r hp]
  · apply le_iInf
    intro w
    apply le_iInf
    intro hw
    apply le_iInf
    intro hc
    exact ENNReal.ofReal_le_ofReal (residual_ratio_lower W r hp w hw hc)

theorem residualCorrelationCost_eq :
    residualCorrelationCost W r =
      if W.starProjection r = 0 then ⊤
      else ENNReal.ofReal (1 / ‖W.starProjection r‖ ^ 2) := by
  split_ifs with hp
  · exact residualCorrelationCost_zero W r hp
  · exact residualCorrelationCost_nonzero W r hp

theorem normalized_cost_bound_iff (hr : r ≠ 0) (K : ℝ) (hK : 0 < K) :
    (∃ w ∈ W, inner ℝ r w ≠ 0 ∧
      ‖r‖ ^ 2 * (‖w‖ ^ 2 / (inner ℝ r w) ^ 2) ≤ K) ↔
      ‖r‖ ^ 2 / K ≤ ‖W.starProjection r‖ ^ 2 := by
  have hrpos : 0 < ‖r‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hr)
  constructor
  · rintro ⟨w, hw, hc, hcost⟩
    have hp : W.starProjection r ≠ 0 := by
      intro hp
      exact projection_zero_infeasible W r hp ⟨w, hw, hc⟩
    have hpos : 0 < ‖W.starProjection r‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hp)
    have hlo := mul_le_mul_of_nonneg_left
      (residual_ratio_lower W r hp w hw hc) (le_of_lt hrpos)
    have hdiv : ‖r‖ ^ 2 / ‖W.starProjection r‖ ^ 2 ≤ K := by
      simpa only [mul_one_div] using hlo.trans hcost
    exact (div_le_iff₀ hK).mpr (by
      have hh := (div_le_iff₀ hpos).mp hdiv
      simpa only [mul_comm] using hh)
  · intro hproj
    have hpos : 0 < ‖W.starProjection r‖ ^ 2 :=
      lt_of_lt_of_le (div_pos hrpos hK) hproj
    have hp : W.starProjection r ≠ 0 := by
      intro hp
      simpa [hp] using hpos
    refine ⟨W.starProjection r, W.starProjection_apply_mem r, ?_, ?_⟩
    · rw [projected_self_correlation]
      exact ne_of_gt hpos
    · rw [residual_ratio_attained W r hp, mul_one_div]
      apply (div_le_iff₀ hpos).mpr
      have hh := (div_le_iff₀ hK).mp hproj
      simpa only [mul_comm] using hh

theorem logarithmic_cost_bound_iff (hr : r ≠ 0) (C L : ℝ)
    (hC : 0 < C) (hL : 1 < L) :
    (∃ w ∈ W, inner ℝ r w ≠ 0 ∧
      ‖r‖ ^ 2 * (‖w‖ ^ 2 / (inner ℝ r w) ^ 2) ≤ C * Real.log L) ↔
      ‖r‖ ^ 2 / (C * Real.log L) ≤ ‖W.starProjection r‖ ^ 2 :=
  normalized_cost_bound_iff W r hr _ (mul_pos hC (Real.log_pos hL))


theorem residualCorrelationCost_inverse :
    residualCorrelationCost W r = (ENNReal.ofReal (‖W.starProjection r‖ ^ 2))⁻¹ := by
  by_cases hp : W.starProjection r = 0
  · rw [residualCorrelationCost_zero W r hp]
    simp [hp]
  · rw [residualCorrelationCost_nonzero W r hp, one_div]
    exact ENNReal.ofReal_inv_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hp))

end RiemannResearch.Analysis.CorrelationCorrection
