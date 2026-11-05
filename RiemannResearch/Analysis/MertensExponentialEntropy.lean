/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp

/-!
# Exponential Mertens envelopes

Scalar estimates for the loss ε (1 + log (1/ε)) in the complete Möbius
head-energy inequality. These estimates apply to an arbitrary real argument.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- Exponential relative error has an exact elementary entropy expression. -/
theorem exponential_entropy_eq (u : ℝ) :
    Real.exp (-u) * (1 + Real.log (1 / Real.exp (-u))) =
      Real.exp (-u) * (1 + u) := by
  simp [one_div, Real.log_inv, Real.log_exp]

/-- Every strictly smaller exponent is retained, with an explicit constant.
This is a scalar bound and uses no arithmetic assumption. -/
theorem exponential_entropy_le
    (b c u : ℝ) (hc : 0 ≤ c) (hcb : c < b) :
    Real.exp (-b * u) * (1 + Real.log (1 / Real.exp (-b * u))) ≤
      (b / (b - c)) * Real.exp (-c * u) := by
  have hbc : 0 < b - c := sub_pos.mpr hcb
  have hk : 1 ≤ b / (b - c) := (le_div_iff₀ hbc).mpr (by linarith)
  have hlinear : 1 + b * u ≤ (b / (b - c)) * (1 + (b - c) * u) := by
    have hid : (b / (b - c)) * (1 + (b - c) * u) = b / (b - c) + b * u := by
      field_simp [ne_of_gt hbc]
    rw [hid]
    linarith
  have he : 1 + b * u ≤ (b / (b - c)) * Real.exp ((b - c) * u) := by
    apply hlinear.trans
    apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) hk)
    linarith [Real.add_one_le_exp ((b - c) * u)]
  have hlog : Real.log (1 / Real.exp (-b * u)) = b * u := by
    simp [one_div, Real.log_inv, Real.log_exp]
  rw [hlog]
  calc
    _ ≤ Real.exp (-b * u) * ((b / (b - c)) * Real.exp ((b - c) * u)) :=
      mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ = (b / (b - c)) * Real.exp (-c * u) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring

/-- A simple effective threshold guarantees the small-error energy premise. -/
theorem exponential_entropy_small (u : ℝ) (hu : 6 ≤ u) :
    Real.exp (-u) * (1 + Real.log (1 / Real.exp (-u))) ≤ 1 / 2 := by
  have h := exponential_entropy_le 1 (1 / 2) u (by norm_num) (by norm_num)
  norm_num at h
  have hfour : (4 : ℝ) ≤ Real.exp (u / 2) := by
    linarith [Real.add_one_le_exp (u / 2)]
  have hexp : Real.exp (-(u / 2)) ≤ (1 : ℝ) / 4 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hfour
  have hid : -((1 / 2 : ℝ) * u) = -(u / 2) := by ring
  rw [hid] at h
  rw [exponential_entropy_eq]
  linarith

end RiemannResearch.Analysis
