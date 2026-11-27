/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualBGSTBDensity
import RiemannResearch.Analysis.ActualZeroCountNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The Selberg endpoint with and without the saving in (1.7)

BGSTB, <https://arxiv.org/abs/2306.04799>, equations (1.6) and (1.7).
The latter is identified there as Selberg's conjecture. Here its estimate
at the moving endpoint is a hypothesis. We compare both majorants with
the actual number of positive-height zero occurrences divided by exp(1).
-/

noncomputable section
open Filter Asymptotics Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The fixed factor exp(-a/2) is the exact evaluation of the Selberg
power at scaled displacement 1/2. -/
theorem selberg_moving_endpoint_power {T : ℝ} (hT : 1 < T) (a : ℝ) :
    T ^ (1 - a * ((1 / 2 + 1 / (2 * Real.log T)) - 1 / 2)) = T * Real.exp (-a / 2) := by
  have hL := (Real.log_pos hT).ne'
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hT),
    show Real.log T * (1 - a * ((1 / 2 + 1 / (2 * Real.log T)) - 1 / 2)) =
        Real.log T + -a / 2 by field_simp [hL]; ring,
    Real.exp_add, Real.exp_log (zero_lt_one.trans hT)]

/-- The one-logarithm Selberg majorant divided by N(T)/e has a strictly
positive limit for every fixed a. -/
theorem selberg_endpoint_majorant_div_count_limit (a : ℝ) :
    Tendsto (fun T : ℝ => (T * Real.log T * Real.exp (-a / 2)) / ((Ncount 0 T : ℝ) / Real.exp 1))
      atTop (𝓝 (2 * Real.pi * Real.exp (1 - a / 2))) := by
  let c := 2 * Real.pi * Real.exp (1 - a / 2)
  have h := (tendsto_count_div_mainTerm.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).const_mul c
  simp only [inv_one, mul_one] at h
  refine h.congr' ?_
  filter_upwards with T
  dsimp [c]
  rw [show 1 - a / 2 = 1 + -a / 2 by ring, Real.exp_add]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Real.pi_ne_zero]

/-- At a = 2 the one-logarithm endpoint majorant has limiting ratio 2π. -/
theorem slope_two_endpoint_majorant_div_count_limit :
    Tendsto (fun T : ℝ => (T * Real.log T / Real.exp 1) / ((Ncount 0 T : ℝ) / Real.exp 1))
      atTop (𝓝 (2 * Real.pi)) := by
  have h := selberg_endpoint_majorant_div_count_limit 2
  rw [show -(2 : ℝ) / 2 = -1 by norm_num, show 1 - (2 : ℝ) / 2 = 0 by norm_num,
    Real.exp_zero, mul_one, Real.exp_neg] at h
  simpa only [div_eq_mul_inv] using h

/-- An eventual endpoint estimate with the extra square-root saving
from (1.7) gives little-o of N(T)/e. -/
theorem selberg_endpoint_isLittleO_count_of_loglog_saving {a C : ℝ}
    (h : ∀ᶠ T : ℝ in atTop,
      rightInclusiveCount T (1 / 2 + 1 / (2 * Real.log T)) ≤
        C * (T * Real.log T * Real.exp (-a / 2)) / Real.sqrt (Real.log (Real.log T))) :
    (fun T : ℝ => rightInclusiveCount T (1 / 2 + 1 / (2 * Real.log T))) =o[atTop]
      (fun T : ℝ => (Ncount 0 T : ℝ) / Real.exp 1) := by
  apply isLittleO_count_div_exp_of_height_log
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have hden := Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have hz : Tendsto (fun T : ℝ => (C * Real.exp (-a / 2)) / Real.sqrt (Real.log (Real.log T)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  filter_upwards [h, hz.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℝ)] with T hb he hT
  have hp := (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)).le
  simp only [Real.norm_eq_abs, abs_of_nonneg (rightInclusiveCount_nonneg _ _), abs_of_nonneg hp]
  apply hb.trans
  calc
    _ = (C * Real.exp (-a / 2) / Real.sqrt (Real.log (Real.log T))) * (T * Real.log T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he.le hp

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.selberg_endpoint_isLittleO_count_of_loglog_saving' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms selberg_endpoint_isLittleO_count_of_loglog_saving

end RiemannResearch.Analysis.ActualZeroOrdinate
