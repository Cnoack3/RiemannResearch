/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A nonzero probe with vanishing cost forces norm divergence

Source: the user-requested signed-sieve investigation, 21 October 2026.
This generic scalar consumer turns a vanishing prime-jump probe cost into
complete norm divergence.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- If a fixed nonzero probe is recovered up to a vanishing remainder, while
its norm cost tends to zero, every nonnegative realizing norm tends to infinity.
The coefficient and nonnegativity conditions need only hold eventually. -/
theorem tendsto_atTop_of_vanishing_probe_cost
    (R z d : ℕ → ℝ) (T : ℝ) (hT : T ≠ 0)
    (hz : Tendsto z atTop (𝓝 0))
    (hd : Tendsto d atTop (𝓝 0))
    (hR : ∀ᶠ n in atTop, 0 ≤ R n)
    (hd_nonneg : ∀ᶠ n in atTop, 0 ≤ d n)
    (hcost : ∀ᶠ n in atTop, |T - z n| ≤ d n * R n) :
    Tendsto R atTop atTop := by
  have hTpos : 0 < |T| := abs_pos.mpr hT
  apply tendsto_atTop.2
  intro b
  by_cases hb : b ≤ 0
  · filter_upwards [hR] with n hRn
    exact hb.trans hRn
  · have hbpos : 0 < b := lt_of_not_ge hb
    obtain ⟨Nz, hNz⟩ := Metric.tendsto_atTop.1 hz (|T| / 2) (by positivity)
    obtain ⟨Nd, hNd⟩ := Metric.tendsto_atTop.1 hd
      (|T| / (2 * b)) (by positivity)
    filter_upwards [hd_nonneg, hcost, eventually_ge_atTop Nz,
      eventually_ge_atTop Nd] with n hdn hcostn hnz hnd
    have hzn : |z n| < |T| / 2 := by
      simpa only [Real.dist_eq, sub_zero] using hNz n hnz
    have hdabs : |d n| < |T| / (2 * b) := by
      simpa only [Real.dist_eq, sub_zero] using hNd n hnd
    have hdsmall : d n < |T| / (2 * b) :=
      (le_abs_self (d n)).trans_lt hdabs
    have hdscaled : d n * (2 * b) < |T| :=
      (lt_div_iff₀ (by positivity : 0 < 2 * b)).mp hdsmall
    have htriangle : |T| ≤ |T - z n| + |z n| := by
      simpa only [sub_add_cancel] using abs_add_le (T - z n) (z n)
    by_contra hRb
    have hRb' : R n < b := lt_of_not_ge hRb
    have hprod : d n * R n ≤ d n * b :=
      mul_le_mul_of_nonneg_left hRb'.le hdn
    nlinarith

end RiemannResearch.Analysis
