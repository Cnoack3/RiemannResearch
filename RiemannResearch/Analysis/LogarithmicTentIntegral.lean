import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weighted integrals of the binary root tent

Source: user-provided `DyadicTentTerminalVerification20260910(1).md`
and the September 10, 2026 continuation. This integral supplies the exact
zero-frequency value for the actual binary residue boundary.

The real tent is normalized to have height one, support `[a,a+2]`, and
apex at `a+1`.  Its integral against `dx/x` is the second difference of
`x * log x`.  This is an exact finite identity; no all-scale estimate or
Riemann-hypothesis assumption enters the statement.
-/

noncomputable section

open MeasureTheory

namespace RiemannResearch.Analysis

def rootTent (a x : ℝ) : ℝ := max 0 (1 - |x - (a + 1)|)

theorem continuous_rootTent (a : ℝ) : Continuous (rootTent a) := by
  unfold rootTent
  fun_prop

theorem rootTent_eq_left {a x : ℝ} (hax : a ≤ x) (hxa : x ≤ a + 1) :
    rootTent a x = x - a := by
  unfold rootTent
  rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
  ring

theorem rootTent_eq_right {a x : ℝ} (hax : a + 1 ≤ x) (hxa : x ≤ a + 2) :
    rootTent a x = a + 2 - x := by
  unfold rootTent
  rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  ring

theorem rootTent_eq_zero_of_le {a x : ℝ} (hx : x ≤ a) : rootTent a x = 0 := by
  unfold rootTent
  rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]

theorem rootTent_eq_zero_of_ge {a x : ℝ} (hx : a + 2 ≤ x) : rootTent a x = 0 := by
  unfold rootTent
  rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]

theorem rootTent_nonneg (a x : ℝ) : 0 ≤ rootTent a x := le_max_left _ _

private theorem inv_intervalIntegrable_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => 1 / x) volume a b := by
  apply intervalIntegral.intervalIntegrable_one_div _ continuousOn_id
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact ne_of_gt (lt_of_lt_of_le ha hx.1)

theorem rootTent_div_intervalIntegrable {a b c : ℝ} (hb : 0 < b) (hbc : b ≤ c) :
    IntervalIntegrable (fun x => rootTent a x / x) volume b c := by
  apply ContinuousOn.intervalIntegrable
  apply (continuous_rootTent a).continuousOn.div continuousOn_id
  intro x hx
  rw [Set.uIcc_of_le hbc] at hx
  exact ne_of_gt (lt_of_lt_of_le hb hx.1)

theorem integral_rootTent_div_left {a : ℝ} (ha : 0 < a) :
    (∫ x in a..a + 1, rootTent a x / x) =
      1 - a * (Real.log (a + 1) - Real.log a) := by
  have ha1 : 0 < a + 1 := by linarith
  have hi := inv_intervalIntegrable_of_pos ha (show a ≤ a + 1 by linarith)
  calc
    (∫ x in a..a + 1, rootTent a x / x) =
        ∫ x in a..a + 1, (1 - a * (1 / x)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (show a ≤ a + 1 by linarith)] at hx
      dsimp only
      rw [rootTent_eq_left hx.1 hx.2]
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
      field_simp [hx0]
    _ = 1 - a * (Real.log (a + 1) - Real.log a) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hi.const_mul a),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos ha ha1,
        Real.log_div (ne_of_gt ha1) (ne_of_gt ha)]
      simp

theorem integral_rootTent_div_right {a : ℝ} (ha : 0 < a) :
    (∫ x in a + 1..a + 2, rootTent a x / x) =
      (a + 2) * (Real.log (a + 2) - Real.log (a + 1)) - 1 := by
  have ha1 : 0 < a + 1 := by linarith
  have ha2 : 0 < a + 2 := by linarith
  have hi := inv_intervalIntegrable_of_pos ha1 (show a + 1 ≤ a + 2 by linarith)
  calc
    (∫ x in a + 1..a + 2, rootTent a x / x) =
        ∫ x in a + 1..a + 2, ((a + 2) * (1 / x) - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (show a + 1 ≤ a + 2 by linarith)] at hx
      dsimp only
      rw [rootTent_eq_right hx.1 hx.2]
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha1 hx.1)
      field_simp [hx0]
    _ = (a + 2) * (Real.log (a + 2) - Real.log (a + 1)) - 1 := by
      rw [intervalIntegral.integral_sub (hi.const_mul (a + 2)) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        integral_one_div_of_pos ha1 ha2,
        Real.log_div (ne_of_gt ha2) (ne_of_gt ha1)]
      simp
      ring

theorem integral_rootTent_div {a : ℝ} (ha : 0 < a) :
    (∫ x in a..a + 2, rootTent a x / x) =
      a * Real.log a - 2 * (a + 1) * Real.log (a + 1) +
        (a + 2) * Real.log (a + 2) := by
  have hiL : IntervalIntegrable (fun x => rootTent a x / x) volume a (a + 1) :=
    rootTent_div_intervalIntegrable ha (by linarith)
  have hiR : IntervalIntegrable (fun x => rootTent a x / x) volume (a + 1) (a + 2) :=
    rootTent_div_intervalIntegrable (by linarith) (by linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals hiL hiR,
    integral_rootTent_div_left ha, integral_rootTent_div_right ha]
  ring

end RiemannResearch.Analysis
