/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CountableJumpEnergy
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# An anchored square-integrability bound from complete pair energy

Source: countable prime-resampling continuation, 27 October 2026.
An atom of positive mass controls the constant part without any prior
integrability assumption. Every sum is ENNReal-valued.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.Analysis.AnchoredPairEnergy
open RiemannResearch.Analysis.CountableJumpEnergy
variable {α : Type*}

def pairWeight (w : α → ℝ≥0∞) (x y : α) : ℝ≥0∞ := w x * w y

/-- The positive anchor has reciprocal mass `c`; no first or second moment
of `g` is assumed. -/
theorem squareEnergy_le_pairEnergy_anchor
    (w : α → ℝ≥0∞) (hw : ∑' x, w x = 1) (a : α)
    (c : ℝ≥0∞) (hca : c * w a = 1) (g : α → ℝ) :
    (∑' x, w x * ENNReal.ofReal (g x ^ 2)) ≤
      (4 * c) * countableJumpEnergy (pairWeight w) g +
        2 * ENNReal.ofReal (g a ^ 2) := by
  have hfour (x : α) : (4 : ℝ≥0∞) * ENNReal.ofReal ((g x - g a) ^ 2 / 2) =
      2 * ENNReal.ofReal ((g x - g a) ^ 2) := by
    rw [← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hpoint (x : α) : w x * ENNReal.ofReal (g x ^ 2) ≤
      (4 * c) * (w x * w a * ENNReal.ofReal ((g x - g a) ^ 2 / 2)) +
        w x * (2 * ENNReal.ofReal (g a ^ 2)) := by
    have he : (4 * c) * (w x * w a * ENNReal.ofReal ((g x - g a) ^ 2 / 2)) =
        w x * (2 * ENNReal.ofReal ((g x - g a) ^ 2)) := by
      calc
        _ = w x * (c * w a) *
            (4 * ENNReal.ofReal ((g x - g a) ^ 2 / 2)) := by ac_rfl
        _ = _ := by rw [hca, mul_one, hfour]
    rw [he, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ zero_le
    calc
      _ ≤ ENNReal.ofReal (2 * (g x - g a) ^ 2 + 2 * g a ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [sq_nonneg (g x - 2 * g a)]
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity : 0 ≤ 2 * (g x - g a) ^ 2)
            (by positivity : 0 ≤ 2 * g a ^ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [ENNReal.ofReal_ofNat]
  have hcol : (∑' x, w x * w a * ENNReal.ofReal ((g x - g a) ^ 2 / 2)) ≤
      countableJumpEnergy (pairWeight w) g := by
    exact ENNReal.tsum_le_tsum (fun x => ENNReal.le_tsum a)
  calc
    _ ≤ ∑' x, ((4 * c) *
          (w x * w a * ENNReal.ofReal ((g x - g a) ^ 2 / 2)) +
        w x * (2 * ENNReal.ofReal (g a ^ 2))) := ENNReal.tsum_le_tsum hpoint
    _ = (4 * c) *
          (∑' x, w x * w a * ENNReal.ofReal ((g x - g a) ^ 2 / 2)) +
        2 * ENNReal.ofReal (g a ^ 2) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hw, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hcol zero_le) le_rfl

theorem squareEnergy_ne_top_of_pairEnergy_ne_top
    (w : α → ℝ≥0∞) (hw : ∑' x, w x = 1) (a : α)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (hca : c * w a = 1) (g : α → ℝ)
    (hD : countableJumpEnergy (pairWeight w) g ≠ ⊤) :
    (∑' x, w x * ENNReal.ofReal (g x ^ 2)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (squareEnergy_le_pairEnergy_anchor w hw a c hca g)
  finiteness

end RiemannResearch.Analysis.AnchoredPairEnergy
