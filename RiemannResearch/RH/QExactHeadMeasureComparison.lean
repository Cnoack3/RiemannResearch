/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact-head asymptotic comparison of the Q and Pareto metrics

The physical weights differ by the multiplier n/(n+1). On a vector whose
physical coordinates 1,...,H vanish, the complete metric defect is therefore
at most 1/(H+2) of the unnormalized Q energy. No legal approximation or
all-stage energy provider is assumed.

Source: the user's CRT/Pareto epsilon-convergence question. The proof uses
QShiftedReciprocal.pareto_inner_identity and the positive coordinate multiplier;
no replacement of complete weighted Gram entries by uniform entries is made.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QExactHeadMeasureComparison
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QShiftedReciprocal

theorem pareto_norm_sq_exact (f : QHilbert) :
    ‖toPareto f‖ ^ 2 = zetaTwo * (‖f‖ ^ 2 - inner ℝ f (B f)) := by
  simpa only [real_inner_self_eq_norm_sq] using pareto_inner_identity f f

/-- Physical sites 1,...,H correspond to normalized coordinates 0,...,H-1. -/
theorem B_inner_le_of_head_zero (f : QHilbert) (H : ℕ)
    (hf : ∀ k : ℕ, 0 < k → k ≤ H → qSequence f k = 0) :
    inner ℝ f (B f) ≤ ‖f‖ ^ 2 / ((H : ℝ) + 2) := by
  have hsB : Summable (fun n : ℕ => (f n) ^ 2 / ((n : ℝ) + 2)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _
      (qCoordinate_square_summable f)
    intro n
    exact div_le_self (sq_nonneg _) (by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  rw [B_inner_tsum, qNorm_sq, ← tsum_div_const]
  apply hsB.tsum_le_tsum _
    ((qCoordinate_square_summable f).div_const ((H : ℝ) + 2))
  intro n
  by_cases hn : n < H
  · have he := hf (n + 1) (Nat.succ_pos _) (by omega)
    have hne : Real.sqrt (qWeight n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))
    have hz : f n = 0 := by
      have hd : f n / Real.sqrt (qWeight n) = 0 := by
        simpa only [qSequence_succ] using he
      exact (div_eq_zero_iff.mp hd).resolve_right hne
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), zero_div, le_refl]
  · apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have hHn : (H : ℝ) ≤ n := by exact_mod_cast (show H ≤ n by omega)
    linarith

/-- The exact omitted correction is positive and becomes small on a moving head. -/
theorem zero_head_metric_defect (f : QHilbert) (H : ℕ)
    (hf : ∀ k : ℕ, 0 < k → k ≤ H → qSequence f k = 0) :
    0 ≤ zetaTwo * ‖f‖ ^ 2 - ‖toPareto f‖ ^ 2 ∧
    zetaTwo * ‖f‖ ^ 2 - ‖toPareto f‖ ^ 2 ≤
      zetaTwo * ‖f‖ ^ 2 / ((H : ℝ) + 2) := by
  have he := pareto_norm_sq_exact f
  have hp := B_positive f
  have hb := B_inner_le_of_head_zero f H hf
  have hm := mul_le_mul_of_nonneg_left hb zetaTwo_pos.le
  constructor
  · nlinarith [mul_nonneg zetaTwo_pos.le hp]
  · nlinarith [show zetaTwo * (‖f‖ ^ 2 / ((H : ℝ) + 2)) =
        zetaTwo * ‖f‖ ^ 2 / ((H : ℝ) + 2) by ring]

theorem zero_head_measure_comparison (f : QHilbert) (H : ℕ)
    (hf : ∀ k : ℕ, 0 < k → k ≤ H → qSequence f k = 0) :
    zetaTwo * (((H : ℝ) + 1) / ((H : ℝ) + 2)) * ‖f‖ ^ 2 ≤
      ‖toPareto f‖ ^ 2 ∧
    ‖toPareto f‖ ^ 2 ≤ zetaTwo * ‖f‖ ^ 2 := by
  have hb := zero_head_metric_defect f H hf
  have he : zetaTwo * (((H : ℝ) + 1) / ((H : ℝ) + 2)) * ‖f‖ ^ 2 =
      zetaTwo * ‖f‖ ^ 2 - zetaTwo * ‖f‖ ^ 2 / ((H : ℝ) + 2) := by
    have hne : (H : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [he]
  constructor <;> linarith

/-- In particular this applies to an exact-head error f-qOne, or to two legal
vectors that agree on the head; no uniformity of either family is presumed. -/
theorem matching_head_measure_comparison (f g : QHilbert) (H : ℕ)
    (hh : ∀ k : ℕ, 0 < k → k ≤ H → qSequence f k = qSequence g k) :
    zetaTwo * (((H : ℝ) + 1) / ((H : ℝ) + 2)) * ‖f - g‖ ^ 2 ≤
      ‖toPareto (f - g)‖ ^ 2 ∧
    ‖toPareto (f - g)‖ ^ 2 ≤ zetaTwo * ‖f - g‖ ^ 2 := by
  apply zero_head_measure_comparison
  intro k hk hkH
  change qSequenceLinear (f - g) k = 0
  simp only [map_sub, Pi.sub_apply]
  exact sub_eq_zero.mpr (hh k hk hkH)

end RiemannResearch.RH.QExactHeadMeasureComparison
