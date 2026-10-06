import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
/-!
# Subpolynomial window growth excludes a positive power floor

Source: user-provided Green–Pareto–Schur continuation, Sections 23.1–23.2.
This module verifies the logarithmic growth contradiction. Actual arithmetic
energies and actual Mellin zero detectors are assembled in the RH modules.
No arithmetic subpolynomial-growth estimate is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.SubpolynomialWindow
theorem exponent_le_log_ratio (x E K c a : ℝ)
    (hx : 1 < x) (hE : 0 ≤ E) (hK : 1 ≤ K) (hc : 0 < c)
    (hfloor : c * x ^ a ≤ E + K) :
    a ≤ (Real.log (1+E) + Real.log K - Real.log c) / Real.log x := by
  have hxp : 0 < x := by linarith
  have hKp : 0 < K := by linarith
  have hEp : 0 < 1+E := by linarith
  have hup : E+K ≤ K*(1+E) := by nlinarith
  have hl := Real.log_le_log
    (mul_pos hc (Real.rpow_pos_of_pos hxp a)) (hfloor.trans hup)
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.rpow_pos_of_pos hxp a)),
      Real.log_rpow hxp a,
      Real.log_mul (ne_of_gt hKp) (ne_of_gt hEp)] at hl
  apply (le_div_iff₀ (Real.log_pos hx)).mpr
  linarith

theorem no_positive_power_floor (x E : ℕ → ℝ) (K c a : ℝ)
    (hx : Tendsto x atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hK : 1 ≤ K) (hc : 0 < c) (ha : 0 < a)
    (hsub : Tendsto (fun n => Real.log (1+E n) / Real.log (x n))
      atTop (𝓝 0))
    (hfloor : ∀ᶠ n in atTop, c * (x n)^a ≤ E n + K) : False := by
  have hlog : Tendsto (fun n => Real.log (x n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hconst : Tendsto
      (fun n => (Real.log K - Real.log c) / Real.log (x n))
      atTop (𝓝 0) := hlog.const_div_atTop _
  have hrhs : Tendsto (fun n =>
      (Real.log (1+E n) + Real.log K - Real.log c) / Real.log (x n))
      atTop (𝓝 0) := by
    have h := hsub.add hconst
    convert h using 1
    · ext n
      ring
    · simp
  have hx1 : ∀ᶠ n in atTop, 1 < x n := hx.eventually (eventually_gt_atTop 1)
  have hbound : ∀ᶠ n in atTop,
      a ≤ (Real.log (1+E n) + Real.log K - Real.log c) / Real.log (x n) := by
    filter_upwards [hx1, hfloor] with n hn hfn
    exact exponent_le_log_ratio (x n) (E n) K c a hn (hE n) hK hc hfn
  have hle : a ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hrhs hbound
  linarith

/-- Multiplying a nonnegative budget by a fixed positive constant preserves
the cofinal relative-logarithmic zero-growth condition. The arithmetic
budget inequality remains visible; no provider is asserted here. -/
theorem relativeLog_tendsto_zero_of_scaled_budget
    (C B L : ℕ → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hC : ∀ n, 0 ≤ C n) (hB : ∀ n, 0 ≤ B n)
    (hL : Tendsto L atTop atTop)
    (hbudget : ∀ᶠ n : ℕ in atTop, 1 + C n ≤ A * (1 + B n))
    (hlogB : Tendsto (fun n => Real.log (1 + B n) / Real.log (L n))
      atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (1 + C n) / Real.log (L n))
      atTop (𝓝 0) := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hlogL : Tendsto (fun n => Real.log (L n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hconstant : Tendsto
      (fun n => Real.log A / Real.log (L n)) atTop (𝓝 0) :=
    hlogL.const_div_atTop _
  have hupper : Tendsto
      (fun n => Real.log A / Real.log (L n) +
        Real.log (1 + B n) / Real.log (L n)) atTop (𝓝 0) := by
    simpa only [add_zero] using hconstant.add hlogB
  have hL2 : ∀ᶠ n : ℕ in atTop, 2 ≤ L n :=
    hL.eventually (eventually_ge_atTop 2)
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hL2] with n hn
    have hl : 0 ≤ Real.log (L n) := Real.log_nonneg (by linarith)
    have hc : 0 ≤ Real.log (1 + C n) := Real.log_nonneg (by linarith [hC n])
    exact ha.trans_le (div_nonneg hc hl)
  · intro b hb
    filter_upwards [hL2, hbudget, hupper.eventually (gt_mem_nhds hb)] with n hn hbud hup
    have hl : 0 < Real.log (L n) := Real.log_pos (by linarith)
    have hc0 : 0 < 1 + C n := by linarith [hC n]
    have hb0 : 0 < 1 + B n := by linarith [hB n]
    have hh : Real.log (1 + C n) ≤ Real.log A + Real.log (1 + B n) := by
      calc
        _ ≤ Real.log (A * (1 + B n)) := Real.log_le_log hc0 hbud
        _ = _ := Real.log_mul (ne_of_gt hA0) (ne_of_gt hb0)
    have hratio :
        Real.log (1 + C n) / Real.log (L n) ≤
          Real.log A / Real.log (L n) +
            Real.log (1 + B n) / Real.log (L n) := by
      calc
        _ ≤ (Real.log A + Real.log (1 + B n)) / Real.log (L n) := by
          simpa only [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr hl.le)
        _ = _ := add_div _ _ _
    exact hratio.trans_lt hup

end RiemannResearch.Analysis.SubpolynomialWindow
