import RiemannResearch.RH.MixedCaptureLegalTrials
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Complete Pareto norm of the projected normalized parity packet

Sections 3–5 of the supplied *Pareto Parity Projection* give the projection
identity used for the conductor-8192 integer trial. The packet is scaled inside the projection.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- Norm of the projection of normalized parity onto the closed mixed space. -/
def normalizedParityCapture : ℝ :=
  ‖mixedClosure.starProjection ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2)‖

theorem normalizedParityCapture_sq :
    normalizedParityCapture ^ 2 = 1 / Real.log 2 - 1 / (1 - limitEnergy) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 1 - limitEnergy ≠ 0 := one_sub_limitEnergy_pos.ne'
  rw [normalizedParityCapture, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hL), mul_pow, full_mixed_capture_eq_limitEnergy]
  field_simp [hL.ne', hd]

/-- The gap in squared norms keeps the complete residual. -/
theorem normalizedParityCapture_sq_deficit :
    (1 / Real.log 2 - 1) - normalizedParityCapture ^ 2 =
      limitEnergy / (1 - limitEnergy) := by
  have hd : 1 - limitEnergy ≠ 0 := one_sub_limitEnergy_pos.ne'
  rw [normalizedParityCapture_sq]
  field_simp [hd, (Real.log_pos (show (1:ℝ) < 2 by norm_num)).ne']
  ring

/-- Any complete-energy upper bound below one gives an exact lower bound
for the normalized mixed projection. -/
theorem sqrt_energy_lower_le_normalizedParityCapture {D : ℝ}
    (hE : limitEnergy ≤ D) (hD : D < 1) :
    Real.sqrt (1 / Real.log 2 - 1 / (1-D)) ≤ normalizedParityCapture := by
  have hi := one_div_le_one_div_of_le (sub_pos.mpr hD) (sub_le_sub_left hE 1)
  have hsq : 1 / Real.log 2 - 1 / (1-D) ≤ normalizedParityCapture^2 := by
    rw [normalizedParityCapture_sq]
    exact sub_le_sub_left hi _
  calc
    _ ≤ Real.sqrt (normalizedParityCapture^2) := Real.sqrt_le_sqrt hsq
    _ = normalizedParityCapture := Real.sqrt_sq (norm_nonneg _)

private theorem capture_sq_le_endpoint :
    normalizedParityCapture ^ 2 ≤ 1 / Real.log 2 - 1 := by
  have he : 0 ≤ limitEnergy := sq_nonneg ‖limitResidual‖
  have hd : 0 < 1 - limitEnergy := one_sub_limitEnergy_pos
  rw [← sub_nonneg, normalizedParityCapture_sq_deficit]
  exact div_nonneg he hd.le

theorem normalizedParityCapture_upper :
    normalizedParityCapture ≤ Real.sqrt (1 / Real.log 2 - 1) :=
  Real.le_sqrt_of_sq_le capture_sq_le_endpoint

theorem normalizedParityCapture_eq_upper_iff :
    normalizedParityCapture = Real.sqrt (1 / Real.log 2 - 1) ↔ limitEnergy = 0 := by
  have hr := (sq_nonneg normalizedParityCapture).trans capture_sq_le_endpoint
  have hs := Real.sq_sqrt hr
  have hd : 1 - limitEnergy ≠ 0 := one_sub_limitEnergy_pos.ne'
  constructor
  · intro h
    have hz : limitEnergy / (1 - limitEnergy) = 0 := by
      rw [← normalizedParityCapture_sq_deficit, h, hs, sub_self]
    exact (div_eq_zero_iff.mp hz).resolve_right hd
  · intro h
    have hf := normalizedParityCapture_sq
    rw [h, sub_zero, div_one] at hf
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (hf.trans hs.symm)

theorem riemannHypothesis_of_normalizedParityCapture_eq_upper
    (h : normalizedParityCapture = Real.sqrt (1 / Real.log 2 - 1)) : RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo_norm_eq_one
    (normalizedScreenedTwo_norm_eq_one_iff.mpr (normalizedParityCapture_eq_upper_iff.mp h))

theorem normalizedParityCapture_eq_upper_iff_riemannHypothesis
    (hBD : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    normalizedParityCapture = Real.sqrt (1 / Real.log 2 - 1) ↔ RiemannHypothesis :=
  normalizedParityCapture_eq_upper_iff.trans
    (normalizedScreenedTwo_norm_eq_one_iff.symm.trans
      (normalizedScreenedTwo_norm_eq_one_iff_riemannHypothesis hBD))

/-- The logarithm bounds use 24 terms of the odd-power series at 1/3. -/
private theorem log_two_bounds :
    (693147180559945309417 : ℝ) / 10^21 < Real.log 2 ∧
      Real.log 2 < (693147180559945309418 : ℝ) / 10^21 := by
  have h := Real.sum_range_sub_log_div_le
    (x := (1:ℝ)/3) (by norm_num) 24
  rw [show (1+(1:ℝ)/3)/(1-(1:ℝ)/3) = 2 by norm_num, abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- Strict rational bounds on the exact upper endpoint, interpreted by truncation. -/
theorem parity_endpoint_decimal :
    (66535332034112778 : ℝ) / 10^17 < Real.sqrt (1 / Real.log 2 - 1) ∧
      Real.sqrt (1 / Real.log 2 - 1) < (66535332034112779 : ℝ) / 10^17 := by
  have hL := Real.log_pos (show (1:ℝ)<2 by norm_num)
  have ha := one_div_le_one_div_of_le hL log_two_bounds.2.le
  have hb := one_div_le_one_div_of_le
    (by norm_num : (0:ℝ) < 693147180559945309417 / 10^21) log_two_bounds.1.le
  have hr := (sq_nonneg normalizedParityCapture).trans capture_sq_le_endpoint
  have hs := Real.sq_sqrt hr
  constructor
  · apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [hs]
    exact lt_of_lt_of_le (by norm_num :
      ((66535332034112778 : ℝ)/10^17)^2 < 1/(693147180559945309418/10^21)-1)
      (sub_le_sub_right ha _)
  · apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [hs]
    exact lt_of_le_of_lt (sub_le_sub_right hb _) (by norm_num)

namespace Conductor8192

/-- Scale and head size in the complete integer trial. -/
def energyBudget : ℝ :=
  5845890643391160621199204193718469 / 1152921507828072450000000000000000000

theorem energyBudget_eq_head_add_tail :
    energyBudget =
      5067697348817286 / (10^9 : ℝ)^2 +
      (3 * 112901299^2 + 161141128064221680975) /
        (12 * (10^9 : ℝ)^2 * (2^30+1)) +
      (5074605440756600^2 + 2 * 112901299 * 5074605440756600) /
        (8 * (10^9 : ℝ)^2 * (2^30+1) * (2^30+2)) := by
  norm_num [energyBudget]

/-- The budget of the 8192 trial is strictly smaller than the supplied
conductor-768 complete-energy budget. -/
theorem energyBudget_lt_conductor768 :
    energyBudget < (1987639569969424585050133:ℝ)/293203310455500000000000000 := by
  norm_num [energyBudget]

theorem normalizedParityCapture_lower_of_budget (he : limitEnergy ≤ energyBudget) :
    (66151243224796 : ℝ)/10^14 < normalizedParityCapture := by
  have ha := one_div_le_one_div_of_le (Real.log_pos (show (1:ℝ)<2 by norm_num))
    log_two_bounds.2.le
  have hb := one_div_le_one_div_of_le (by norm_num [energyBudget] : 0 < 1 - energyBudget)
    (sub_le_sub_left he 1)
  apply (sq_lt_sq₀ (by norm_num) (norm_nonneg _)).mp
  change ((66151243224796 : ℝ)/10^14)^2 < normalizedParityCapture ^ 2
  rw [normalizedParityCapture_sq]
  exact lt_of_lt_of_le (by norm_num [energyBudget] :
    ((66151243224796:ℝ)/10^14)^2 <
      1/(693147180559945309418/10^21) - 1/(1-energyBudget)) (sub_le_sub ha hb)

end Conductor8192
end RiemannResearch.RH.Pareto.PrimePowerSchur
