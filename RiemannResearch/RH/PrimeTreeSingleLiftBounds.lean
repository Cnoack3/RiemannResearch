/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-! # A single first lift five on the entire left half of the critical strip

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§3 (the four exact edges and the geometric coefficient tail) and §5.1
(the single-lift multiplier argument). Here the multiplier is divided by the
nonvanishing phase and scale of the leading term. The hypotheses describe
the positive tail and its first moment, explicitly retaining those arithmetic
inputs to the analytic estimate. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.PrimeTreeSingleLiftBounds

/-- Removing the nonvanishing factor 3^(1-s)/2 gives exactly this normalized
form for the U=5 multiplier. Here q indexes the remaining ratios p/3. -/
def fiveFactor (q w : ℕ → ℝ) (s : ℂ) : ℂ :=
  (14 / 15 : ℂ) + (∑' k, (w k : ℂ) * (q k : ℂ) ^ (1 - s)) -
    ((2/3 : ℝ) : ℂ) ^ (1-s)

/-- The four printed edge weights and the remaining geometric estimate
bound the unscaled first moment strictly below 17/20. -/
theorem firstMoment_rational_certificate :
    (4 / 5 + 3 / 65 + 10 / 12415 + 2 / 12415 : ℝ) = 809 / 955 ∧
    (809 / 955 : ℝ) < 17 / 20 := by norm_num

/-- In the paper the supplied moment M is at most (2/15)(17/20).
The bound is uniform in the imaginary coordinate. -/
theorem fiveFactor_norm_lower (q w : ℕ → ℝ) (hq : ∀ k, 1 ≤ q k) (hw : ∀ k, 0 ≤ w k)
    (M : ℝ) (hm : HasSum (fun k => w k * q k) M) (hM : M ≤ 17/150)
    (s : ℂ) (h0 : 0 ≤ s.re) (hh : s.re ≤ 1/2) :
    (1/300 : ℝ) < ‖fiveFactor q w s‖ := by
  let T : ℂ := ∑' k, (w k : ℂ) * (q k : ℂ) ^ (1-s)
  let C : ℂ := ((2/3 : ℝ) : ℂ) ^ (1-s)
  have hT : ‖T‖ ≤ M := by
    apply tsum_of_norm_bounded hm
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw k),
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le (hq k)), Complex.sub_re,
      Complex.one_re]
    apply mul_le_mul_of_nonneg_left _ (hw k)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (hq k) (show 1 - s.re ≤ (1 : ℝ) by linarith)
  have hC : ‖C‖ < 49/60 := by
    dsimp [C]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2/3),
      Complex.sub_re, Complex.one_re]
    calc
      (2/3 : ℝ) ^ (1 - s.re) ≤ (2/3 : ℝ) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ < _ := by rw [← Real.sqrt_eq_rpow, Real.sqrt_lt' (by norm_num : 0 < (49/60 : ℝ))]; norm_num
  have ht : ‖(14 / 15 : ℂ)‖ ≤ ‖fiveFactor q w s‖ + ‖T‖ + ‖C‖ := by
    have he : (14 / 15 : ℂ) = (fiveFactor q w s - T) + C := by
      dsimp [fiveFactor, T, C]
      ring
    calc
      ‖(14 / 15 : ℂ)‖ = ‖(fiveFactor q w s - T) + C‖ := congrArg norm he
      _ ≤ ‖fiveFactor q w s - T‖ + ‖C‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
  rw [norm_div] at ht
  norm_num at ht
  linarith

end RiemannResearch.RH.PrimeTreeSingleLiftBounds
