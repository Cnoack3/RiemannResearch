/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cofinal small relative logarithmic growth excludes power floors

Source: exact-head averaging research agenda, priority 4, 24 October 2026.
This weakens a full logarithmic-ratio limit to arbitrarily small ratios
occurring cofinally. No arithmetic growth estimate is asserted.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.SubpolynomialWindow

/-- A positive power floor is incompatible with arbitrarily small relative
logarithmic growth cofinally. Convergence of the whole ratio is unnecessary. -/
theorem no_positive_power_floor_of_frequently_small_relativeLog
    (x E : ℕ → ℝ) (K c a : ℝ)
    (hx : Tendsto x atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hK : 1 ≤ K) (hc : 0 < c) (ha : 0 < a)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop,
      Real.log (1 + E n) / Real.log (x n) < ε)
    (hfloor : ∀ᶠ n in atTop, c * (x n) ^ a ≤ E n + K) : False := by
  have hlog : Tendsto (fun n => Real.log (x n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hconst : Tendsto
      (fun n => (Real.log K - Real.log c) / Real.log (x n))
      atTop (𝓝 0) := hlog.const_div_atTop _
  have hx1 : ∀ᶠ n in atTop, 1 < x n := hx.eventually (eventually_gt_atTop 1)
  have hconstsmall := hconst.eventually (Iio_mem_nhds (half_pos ha))
  obtain ⟨n, hsn, hxn, hcn, hfn⟩ :=
    ((hsmall (a / 2) (half_pos ha)).and_eventually
      (hx1.and (hconstsmall.and hfloor))).exists
  have hb := exponent_le_log_ratio (x n) (E n) K c a hxn (hE n) hK hc hfn
  have hid : (Real.log (1 + E n) + Real.log K - Real.log c) / Real.log (x n) =
      Real.log (1 + E n) / Real.log (x n) +
        (Real.log K - Real.log c) / Real.log (x n) := by ring
  rw [hid] at hb
  linarith only [hb, hsn, hcn]

end RiemannResearch.Analysis.SubpolynomialWindow
