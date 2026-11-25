import RiemannResearch.RH.MixedCaptureLegalTrials
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The scalar relating the projected constant to the normalized screened packet

Pairing the scalar equation with the projected constant gives its reciprocal
squared norm. Pairing with the normalized screened packet gives its squared norm.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The normalized screened packet is a positive multiple of the projected constant. -/
theorem normalizedScreenedTwo_eq_norm_sq_smul_limitProjection :
    normalizedScreenedTwo = (‖normalizedScreenedTwo‖ ^ 2) • limitProjection := by
  have hu : 0 < ‖normalizedScreenedTwo‖ := zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo
  rw [limitProjection_eq_inv_norm_sq_smul_screenedTwo, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 hu.ne'), one_smul]

/-- Pairing the scalar equation with the projected constant determines the coefficient. -/
theorem normalizedScreenedTwo_projection_scalar {c : ℝ}
    (hc : normalizedScreenedTwo = c • limitProjection) :
    0 < c ∧ 1 = c * ‖limitProjection‖ ^ 2 ∧
      c = 1 / ‖limitProjection‖ ^ 2 ∧ c = ‖normalizedScreenedTwo‖ ^ 2 := by
  have hpair : 1 = c * ‖limitProjection‖ ^ 2 := calc
    1 = inner ℝ limitProjection normalizedScreenedTwo :=
      limitProjection_inner_normalizedScreenedTwo.symm
    _ = inner ℝ limitProjection (c • limitProjection) := congrArg (inner ℝ limitProjection) hc
    _ = c * ‖limitProjection‖ ^ 2 := by rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hp : ‖limitProjection‖ ^ 2 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hpair
    exact one_ne_zero hpair
  have hcNorm : c = ‖normalizedScreenedTwo‖ ^ 2 := by
    have h := congrArg (fun v : ThresholdHilbert => inner ℝ v normalizedScreenedTwo) hc
    simpa only [real_inner_self_eq_norm_sq, real_inner_smul_left,
      limitProjection_inner_normalizedScreenedTwo, mul_one] using h.symm
  have hu : 0 < ‖normalizedScreenedTwo‖ := zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo
  refine ⟨?_, hpair, (eq_div_iff hp).mpr hpair.symm, hcNorm⟩
  rw [hcNorm]
  exact sq_pos_of_pos hu

/-- The projected pair attains Cauchy–Schwarz unconditionally. -/
theorem limitProjection_normalizedScreenedTwo_cauchySchwarz_eq :
    |inner ℝ limitProjection normalizedScreenedTwo| =
      ‖limitProjection‖ * ‖normalizedScreenedTwo‖ := by
  have hu : 0 < ‖normalizedScreenedTwo‖ := zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo
  rw [limitProjection_inner_normalizedScreenedTwo, abs_one,
    limitProjection_eq_inv_norm_sq_smul_screenedTwo, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hu)), mul_assoc, ← pow_two,
    inv_mul_cancel₀ (pow_ne_zero 2 hu.ne')]

end RiemannResearch.RH.Pareto.PrimePowerSchur
