/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QPhysicalTailEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete tails of the centered reciprocal multiplier

Source: direct multiplier comparison for signed regularity localization.
-/

noncomputable section
namespace RiemannResearch.RH.QShiftedReciprocal
open ZetaTwoHilbert QAnnihilatorTailEscape QFiniteSupportDualCriterion

/-- On the complete physical tail m ≥ n+1, centering B at 1/(n+2)
has operator bound 1/(n+2). No finite-tail approximation is used. -/
theorem centered_upperTail_energy_le (f : QHilbert) (n : ℕ) :
    ‖tail n (B f - (1 / ((n : ℝ) + 2)) • f)‖ ^ 2 ≤
      (1 / ((n : ℝ) + 2)) ^ 2 * ‖f‖ ^ 2 := by
  have hsq : ‖tail n (B f - (1 / ((n : ℝ) + 2)) • f)‖ ^ 2 ≤
      ‖(1 / ((n : ℝ) + 2)) • f‖ ^ 2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
      (qCoordinate_square_summable _)
    intro i
    change ((B f - (1 / ((n : ℝ) + 2)) • f) i -
      finiteHead n (B f - (1 / ((n : ℝ) + 2)) • f) i) ^ 2 ≤
      ((1 / ((n : ℝ) + 2)) * f i) ^ 2
    by_cases hi : n ≤ i
    · rw [finiteHead_apply_eq_zero _ _ _ hi, sub_zero]
      change (f i / ((i : ℝ) + 2) -
        (1 / ((n : ℝ) + 2)) * f i) ^ 2 ≤
          ((1 / ((n : ℝ) + 2)) * f i) ^ 2
      have hd : 0 < (n : ℝ) + 2 := by positivity
      have hid : 0 < (i : ℝ) + 2 := by positivity
      have hlo : 0 ≤ 1 / ((i : ℝ) + 2) := by positivity
      have hni : (n : ℝ) + 2 ≤ (i : ℝ) + 2 := by
        have hni' : (n : ℝ) ≤ i := by exact_mod_cast hi
        linarith
      have hhi : 1 / ((i : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
        one_div_le_one_div_of_le hd hni
      have ha : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
      have hc : (1 / ((i : ℝ) + 2) - 1 / ((n : ℝ) + 2)) ^ 2 ≤
          (1 / ((n : ℝ) + 2)) ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (f i))
      convert hm using 1 <;> ring
    · rw [finiteHead_apply_of_lt _ _ _ (by omega), sub_self]
      simpa only [zero_pow (by decide : 2 ≠ 0)] using
        sq_nonneg ((1 / ((n : ℝ) + 2)) * f i)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 / ((n : ℝ) + 2)), mul_pow] at hsq
  exact hsq

end RiemannResearch.RH.QShiftedReciprocal
