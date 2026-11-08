/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive logarithmic variation and subpolynomial growth

Source: user-provided `CanonicalPrimePowerUpdatesResearch20261107(1).md`,
Section 7. The positive-logarithmic-variation condition below is a proposed
weakening of its positive-relative-increment condition. The elementary
telescoping argument proves a conditional growth reduction; it supplies no
arithmetic estimate for the actual canonical sequence.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Real

/-- Total positive variation through the first `N` successive increments. -/
def positiveVariation (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, max (g (n + 1) - g n) 0

/-- The signed increments telescope exactly; decreases are retained here. -/
theorem sum_increments_eq_sub (g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (g (n + 1) - g n)) = g N - g 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem positiveVariation_nonneg (g : ℕ → ℝ) (N : ℕ) :
    0 ≤ positiveVariation g N := by
  unfold positiveVariation
  exact Finset.sum_nonneg (fun n _ => le_max_right (g (n + 1) - g n) 0)

/-- Dropping only negative increments gives a one-sided growth bound. -/
theorem le_initial_add_positiveVariation (g : ℕ → ℝ) (N : ℕ) :
    g N ≤ g 0 + positiveVariation g N := by
  have hs : (∑ n ∈ Finset.range N, (g (n + 1) - g n)) ≤
      positiveVariation g N := by
    unfold positiveVariation
    exact Finset.sum_le_sum (fun n _ => le_max_left (g (n + 1) - g n) 0)
  rw [sum_increments_eq_sub] at hs
  linarith

/-- Sublogarithmic positive variation of `log (1 + E)` forces
subpolynomial growth of a nonnegative energy sequence. -/
theorem log_ratio_tendsto_zero_of_positiveVariation
    (x E : ℕ → ℝ) (hx : Tendsto x atTop atTop)
    (hE : ∀ n, 0 ≤ E n)
    (hvariation : Tendsto
      (fun N => positiveVariation (fun n => Real.log (1 + E n)) N /
        Real.log (x N)) atTop (𝓝 0)) :
    Tendsto (fun N => Real.log (1 + E N) / Real.log (x N))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N => Real.log (x N)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hconstant : Tendsto
      (fun N => Real.log (1 + E 0) / Real.log (x N)) atTop (𝓝 0) :=
    hlog.const_div_atTop _
  have hupper : Tendsto
      (fun N => Real.log (1 + E 0) / Real.log (x N) +
        positiveVariation (fun n => Real.log (1 + E n)) N /
          Real.log (x N)) atTop (𝓝 0) := by
    simpa only [add_zero] using hconstant.add hvariation
  have hx2 : ∀ᶠ N : ℕ in atTop, 2 ≤ x N :=
    hx.eventually (eventually_ge_atTop 2)
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hx2] with N hN
    have hden : 0 ≤ Real.log (x N) := Real.log_nonneg (by linarith)
    have hnum : 0 ≤ Real.log (1 + E N) :=
      Real.log_nonneg (by linarith [hE N])
    exact ha.trans_le (div_nonneg hnum hden)
  · intro b hb
    filter_upwards [hx2, hupper.eventually (gt_mem_nhds hb)] with N hN hup
    have hden : 0 < Real.log (x N) := Real.log_pos (by linarith)
    have hbound := le_initial_add_positiveVariation
      (fun n => Real.log (1 + E n)) N
    have hratio : Real.log (1 + E N) / Real.log (x N) ≤
        Real.log (1 + E 0) / Real.log (x N) +
          positiveVariation (fun n => Real.log (1 + E n)) N /
            Real.log (x N) := by
      calc
        _ ≤ (Real.log (1 + E 0) +
            positiveVariation (fun n => Real.log (1 + E n)) N) /
              Real.log (x N) := by
          simpa only [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right hbound (inv_nonneg.mpr hden.le)
        _ = _ := add_div _ _ _
    exact hratio.trans_lt hup

end Real
