import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact unit-cell energy and its Pareto quadratic form

Source: user-provided handoff Sections 18--19, and the elementary
unit-cell integration/completing-square proof developed from it.
The cell value `P` may later be instantiated by the right-continuous
Chebyshev function, constant away from the endpoints of an integer cell.
No RH assumption enters any declaration in this module.
-/

open Set MeasureTheory
open scoped Interval

namespace RiemannResearch.ChebyshevCell

noncomputable def energy (a P : ℝ) : ℝ :=
  ∫ x in a..a + 1, (P - x) ^ 2 / x ^ 2

noncomputable def center (a : ℝ) : ℝ :=
  a * (a + 1) * Real.log ((a + 1) / a)

noncomputable def defect (a : ℝ) : ℝ :=
  1 - a * (a + 1) * Real.log ((a + 1) / a) ^ 2

private theorem pos_on_cell {a x : ℝ} (ha : 0 < a)
    (hx : x ∈ uIcc a (a + 1)) : 0 < x := by
  rw [uIcc_of_le (by linarith : a ≤ a + 1)] at hx
  exact lt_of_lt_of_le ha hx.1

theorem integrable_energy {a : ℝ} (ha : 0 < a) (P : ℝ) :
    IntervalIntegrable (fun x : ℝ => (P - x) ^ 2 / x ^ 2) volume a (a + 1) := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  exact (((continuousAt_const.sub continuousAt_id).pow 2).div
    (continuousAt_id.pow 2) (pow_ne_zero 2 (pos_on_cell ha hx).ne')).continuousWithinAt

theorem energy_formula {a : ℝ} (ha : 0 < a) (P : ℝ) :
    energy a P = P ^ 2 / (a * (a + 1))
      - 2 * P * Real.log ((a + 1) / a) + 1 := by
  have ha1 : 0 < a + 1 := by linarith
  have hd : ∀ x ∈ uIcc a (a + 1),
      HasDerivAt (fun y : ℝ => -(P ^ 2 / y) - (2 * P) * Real.log y + y)
        ((P - x) ^ 2 / x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := (pos_on_cell ha hx).ne'
    have h := ((((hasDerivAt_const x (P ^ 2)).div (hasDerivAt_id x) hx0).neg).sub
      ((Real.hasDerivAt_log hx0).const_mul (2 * P))).add (hasDerivAt_id x)
    convert h using 1 <;> first | rfl | (dsimp; field_simp [hx0]; ring)
  unfold energy
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (integrable_energy ha P)]
  rw [Real.log_div ha1.ne' ha.ne']
  field_simp [ha.ne', ha1.ne']
  ring

theorem energy_complete_square {a : ℝ} (ha : 0 < a) (P : ℝ) :
    energy a P = (P - center a) ^ 2 / (a * (a + 1)) + defect a := by
  rw [energy_formula ha]
  unfold center defect
  have ha1 : a + 1 ≠ 0 := by linarith
  field_simp [ha.ne', ha1]
  ring

theorem energy_nonneg {a : ℝ} (_ha : 0 < a) (P : ℝ) :
    0 ≤ energy a P := by
  apply intervalIntegral.integral_nonneg_of_forall (by linarith : a ≤ a + 1)
  intro x
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem energy_at_center {a : ℝ} (ha : 0 < a) :
    energy a (center a) = defect a := by
  simp [energy_complete_square ha]

theorem defect_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ defect a := by
  rw [← energy_at_center ha]
  exact energy_nonneg ha _

theorem center_minimizes {a : ℝ} (ha : 0 < a) (P : ℝ) :
    defect a ≤ energy a P := by
  rw [energy_complete_square ha]
  have h : 0 ≤ (P - center a) ^ 2 / (a * (a + 1)) := by positivity
  linarith

theorem center_mem {a : ℝ} (ha : 0 < a) : center a ∈ Icc a (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  have hratio : 0 < (a + 1) / a := div_pos ha1 ha
  have hmul : 0 ≤ a * (a + 1) := by positivity
  have hlo := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hratio) hmul
  have hhi := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio) hmul
  have hleft : a * (a + 1) * (1 - ((a + 1) / a)⁻¹) = a := by
    field_simp [ha.ne', ha1.ne']
    ring
  have hright : a * (a + 1) * ((a + 1) / a - 1) = a + 1 := by
    field_simp [ha.ne', ha1.ne']
    ring
  rw [hleft] at hlo
  rw [hright] at hhi
  exact ⟨hlo, hhi⟩

private theorem midpoint_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in a..a + 1, (a + 1 / 2 - x) ^ 2 / a ^ 2) = 1 / (12 * a ^ 2) := by
  have hi : IntervalIntegrable
      (fun x : ℝ => (a + 1 / 2 - x) ^ 2 / a ^ 2) volume a (a + 1) := by
    exact (((continuous_const.sub continuous_id).pow 2).div_const _).intervalIntegrable _ _
  have hd : ∀ x ∈ uIcc a (a + 1),
      HasDerivAt (fun y : ℝ => -(a + 1 / 2 - y) ^ 3 / (3 * a ^ 2))
        ((a + 1 / 2 - x) ^ 2 / a ^ 2) x := by
    intro x hx
    have h := (((((hasDerivAt_const x (a + 1 / 2)).sub
      (hasDerivAt_id x)).pow 3).neg).div_const (3 * a ^ 2))
    convert h using 1 <;> first | rfl | (dsimp; field_simp [ha.ne']; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  field_simp [ha.ne']
  ring

theorem defect_le {a : ℝ} (ha : 0 < a) :
    defect a ≤ 1 / (12 * a ^ 2) := by
  have hi : IntervalIntegrable
      (fun x : ℝ => (a + 1 / 2 - x) ^ 2 / a ^ 2) volume a (a + 1) := by
    exact (((continuous_const.sub continuous_id).pow 2).div_const _).intervalIntegrable _ _
  have hm : energy a (a + 1 / 2) ≤
      ∫ x in a..a + 1, (a + 1 / 2 - x) ^ 2 / a ^ 2 := by
    apply intervalIntegral.integral_mono_on (by linarith : a ≤ a + 1)
      (integrable_energy ha _) hi
    intro x hx
    apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos ha)
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1)
      (by linarith [hx.1] : 0 ≤ x + a)]
  exact (center_minimizes ha _).trans (hm.trans_eq (midpoint_integral ha))

end RiemannResearch.ChebyshevCell
