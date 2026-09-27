/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.StretchedExponentialBounds

/-!
# Finite comparisons for logarithmic-product powers

See `RH/MertensStretchedContinuation20260927.md` for the provider audit,
finite optimization, and scope of the result.
-/

noncomputable section
namespace RiemannResearch.Analysis

/-- The optimized stretched-log profile remains sublinear in its argument. -/
theorem logProductPower_le_self {β L : ℝ} (hβ : 0 ≤ β) (hβ2 : β ≤ 1 / 2)
    (hL : 6 ≤ L) :
    logProductPower β L ≤ L := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlog : Real.log L ≤ L := by
    linarith [Real.log_le_sub_one_of_pos hL0]
  have hprod : L * Real.log L ≤ L ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  unfold logProductPower
  calc
    _ ≤ (L ^ (2 : ℝ)) ^ β :=
      Real.rpow_le_rpow (mul_nonneg hL0.le hl0) hprod hβ
    _ = L ^ (2 * β) := by rw [← Real.rpow_mul hL0.le]
    _ ≤ L := Real.rpow_le_self_of_one_le hL1 (by linarith)

/-- Halving the logarithmic argument loses at most a factor four in the
optimized profile; this explicit bound drives the hyperbola cutoff. -/
theorem logProductPower_half_lower {β L J : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hL : 16 ≤ L) (hJ : L / 2 ≤ J) :
    logProductPower β L / 4 ≤ logProductPower β J := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlog2 : 2 * Real.log (2 : ℝ) ≤ Real.log L := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show 4 ≤ L by linarith)
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith
  have hloghalf : Real.log L / 2 ≤ Real.log (L / 2) := by
    rw [Real.log_div hL0.ne' (by norm_num)]
    linarith
  have hbase : (L * Real.log L) / 4 ≤ (L / 2) * Real.log (L / 2) := by
    have h := mul_le_mul_of_nonneg_left hloghalf (by positivity : 0 ≤ L / 2)
    nlinarith
  have hp : ((L * Real.log L) / 4) ^ β ≤ ((L / 2) * Real.log (L / 2)) ^ β :=
    Real.rpow_le_rpow (by positivity) hbase hβ
  rw [Real.div_rpow (by positivity : 0 ≤ L * Real.log L) (by norm_num)] at hp
  have hfour : (4 : ℝ) ^ β ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) hβ1
  calc
    _ ≤ logProductPower β L / (4 : ℝ) ^ β :=
      div_le_div_of_nonneg_left (by unfold logProductPower; positivity)
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) β) hfour
    _ ≤ logProductPower β (L / 2) := hp
    _ ≤ logProductPower β J :=
      logProductPower_mono β hβ (by linarith : 1 ≤ L / 2) hJ

end RiemannResearch.Analysis
