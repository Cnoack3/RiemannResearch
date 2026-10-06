import RiemannResearch.Analysis.HeadTailConditions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Moving absorption gaps for complete signed head-tail identities

Source: user-provided Green-Pareto-Schur continuation, Section 18.
The fixed strict fraction is replaced by a positive stage-dependent gap.
This verifies an implication; the signed arithmetic inequality remains open.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.HeadTailStrengthening

/-- Exact signed absorption, before any absolute-value bound on the head. -/
theorem signed_moving_gap_bound (D H L Z gap : ℝ)
    (hgap : 0 < gap) (hid : D = H + L)
    (hbudget : L ≤ (1-gap)*D + Z) : D ≤ (H+Z)/gap := by
  apply (le_div_iff₀ hgap).mpr
  nlinarith

/-- The gap may tend to zero: only the signed remainder divided by the gap
must vanish. No uniform separation of the fraction from one is required. -/
theorem limit_eq_zero_of_signed_moving_gap
    (D H L Z gap : ℕ → ℝ) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hD : Tendsto D atTop (𝓝 delta))
    (hgap : ∀ᶠ n in atTop, 0 < gap n)
    (hid : ∀ n, D n = H n + L n)
    (hbudget : ∀ᶠ n in atTop, L n ≤ (1-gap n)*D n + Z n)
    (hsmall : Tendsto (fun n => (H n+Z n)/gap n) atTop (𝓝 0)) :
    delta = 0 := by
  have hb : ∀ᶠ n in atTop, D n ≤ (H n+Z n)/gap n := by
    filter_upwards [hgap, hbudget] with n hn hb
    exact signed_moving_gap_bound _ _ _ _ _ hn (hid n) hb
  exact le_antisymm (le_of_tendsto_of_tendsto hD hsmall hb) hdelta

/-- Practical relative head-error version. The entire tail pairing remains
signed, and the positive gap is allowed to vanish at an arbitrary rate. -/
theorem limit_eq_zero_of_head_error_moving_gap
    (D H L E Z gap : ℕ → ℝ) (delta B : ℝ)
    (hdelta : 0 ≤ delta) (hD : Tendsto D atTop (𝓝 delta))
    (hgap : ∀ᶠ n in atTop, 0 < gap n)
    (hid : ∀ n, D n = H n + L n)
    (hhead : ∀ᶠ n in atTop, |H n| ≤ B*E n)
    (hbudget : ∀ᶠ n in atTop, L n ≤ (1-gap n)*D n + Z n)
    (hE : Tendsto (fun n => E n/gap n) atTop (𝓝 0))
    (hZ : Tendsto (fun n => Z n/gap n) atTop (𝓝 0)) :
    delta = 0 := by
  have hup : Tendsto (fun n => B*(E n/gap n)+Z n/gap n)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hE.const_mul B).add hZ
  have hb : ∀ᶠ n in atTop, D n ≤ B*(E n/gap n)+Z n/gap n := by
    filter_upwards [hgap, hbudget, hhead] with n hn hb hh
    have hh' : H n ≤ B*E n := (le_abs_self _).trans hh
    calc
      D n ≤ (H n+Z n)/gap n :=
        signed_moving_gap_bound _ _ _ _ _ hn (hid n) hb
      _ ≤ (B*E n+Z n)/gap n :=
        div_le_div_of_nonneg_right (by linarith) hn.le
      _ = B*(E n/gap n)+Z n/gap n := by ring
  exact le_antisymm (le_of_tendsto_of_tendsto hD hup hb) hdelta

end RiemannResearch.Analysis.HeadTailStrengthening
