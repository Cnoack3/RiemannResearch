import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Power-weight interval energies

Source: user-provided signed energy formula (15.6) in
V_Zeta_Vector_Spaces_Research_2026-09-16.md. The elementary integral comparison
below supports RH/PrimePowerEnergyBounds: a linear discrepancy envelope
produces a telescoping majorant only for exponents s > 2.
-/

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.Analysis.PowerCellEnergy

def powerIntervalWeight (a b s : ℝ) : ℝ := (a ^ (-s) - b ^ (-s)) / s

theorem powerIntervalWeight_nonneg {a b s : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s) :
    0 ≤ powerIntervalWeight a b s := by
  apply div_nonneg _ hs.le
  exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos ha hab (by linarith))

theorem powerIntervalWeight_eq_integral {a b s : ℝ}
    (ha : 0 < a) (hab : a < b) (hs : 0 < s) :
    powerIntervalWeight a b s = ∫ x in a..b, x ^ (-s - 1) := by
  have hz : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab.le]
    intro hx
    exact (not_le_of_gt ha) hx.1
  rw [integral_rpow (Or.inr ⟨by linarith, hz⟩)]
  have he : -s - 1 + 1 = -s := by ring
  rw [he]
  unfold powerIntervalWeight
  rw [div_neg]
  ring

theorem powerIntervalWeight_mul_sq_le {a b s d K : ℝ}
    (ha : 0 < a) (hab : a < b) (hs : 2 < s)
    (hd : d ^ 2 ≤ K ^ 2 * a ^ 2) :
    powerIntervalWeight a b s * d ^ 2 ≤
      K ^ 2 * ((a ^ (2 - s) - b ^ (2 - s)) / (s - 2)) := by
  have hz : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab.le]
    intro hx
    exact (not_le_of_gt ha) hx.1
  have hint (r : ℝ) : IntervalIntegrable (fun x : ℝ => x ^ r) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    rw [uIcc_of_le hab.le] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hcompare : (∫ x in a..b, d ^ 2 * x ^ (-s - 1)) ≤
      ∫ x in a..b, K ^ 2 * x ^ (1 - s) := by
    apply intervalIntegral.integral_mono_on hab.le
      ((hint _).const_mul _) ((hint _).const_mul _)
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    have hax : a ^ 2 ≤ x ^ 2 := by
      nlinarith [hx.1, mul_nonneg (sub_nonneg.mpr hx.1) (add_nonneg ha.le hx0.le)]
    have hd' : d ^ 2 ≤ K ^ 2 * x ^ 2 :=
      hd.trans (mul_le_mul_of_nonneg_left hax (sq_nonneg K))
    have he : x ^ 2 * x ^ (-s - 1) = x ^ (1 - s) := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx0]
      congr 1
      norm_num
      ring
    calc
      _ ≤ (K ^ 2 * x ^ 2) * x ^ (-s - 1) :=
        mul_le_mul_of_nonneg_right hd' (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [mul_assoc, he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← powerIntervalWeight_eq_integral ha hab (by linarith)] at hcompare
  have he : (∫ x in a..b, x ^ (1 - s)) =
      (a ^ (2 - s) - b ^ (2 - s)) / (s - 2) := by
    rw [integral_rpow (Or.inr ⟨by linarith, hz⟩)]
    have h1 : 1 - s + 1 = 2 - s := by ring
    rw [h1]
    have h2 : 2 - s = -(s - 2) := by ring
    rw [h2, div_neg]
    ring
  rw [he] at hcompare
  simpa only [mul_comm] using hcompare


end RiemannResearch.Analysis.PowerCellEnergy
