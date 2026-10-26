/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteAbelSummation
import RiemannResearch.RH.QPolylogMovingHeadEnergy
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Cumulative signed Q cross moments and finite Abel summation

Source: the user's infinite-CRT weighted-energy handoff, priority 2,
26 October 2026. The complete signed identities hold for arbitrary Q vectors.
Ordinary orthogonality supplies a lower bound on cumulative moments. The
weighted Abel expression requires an upper bound on their positive variation;
that additional arithmetic estimate is not proved here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QHeadCrossMoments
open ZetaTwoHilbert QFiniteSupportDualCriterion QAnnihilatorTailEscape
open QPolylogTailEnergy RiemannResearch.Analysis.LogTailWeights

/-- Cumulative ordinary Q cross moment over physical sites `1 ≤ n ≤ H`. -/
def headCross (H : ℕ) (f g : QHilbert) : ℝ :=
  ∑ n ∈ Finset.range (H + 1),
    positiveQWeight n * qSequence f n * qSequence g n

theorem headCross_eq_inner (H : ℕ) (f g : QHilbert) :
    headCross H f g = inner ℝ (finiteHead H f) g := by
  rw [real_inner_comm, inner_finiteHead_eq_sum]
  unfold headCross
  rw [Finset.sum_range_succ']
  simp only [qSequence_zero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro n hn
  exact qSequence_weighted_product f g n

theorem tail_sub (H : ℕ) (f g : QHilbert) :
    tail H (f - g) = tail H f - tail H g := by
  apply lp.ext
  funext n
  change (f n - g n) - finiteHead H (f - g) n =
    (f n - finiteHead H f n) - (g n - finiteHead H g n)
  by_cases hn : n < H
  · rw [finiteHead_apply_of_lt H (f - g) n hn,
      finiteHead_apply_of_lt H f n hn, finiteHead_apply_of_lt H g n hn]
    change (f n - g n) - (f n - g n) = (f n - f n) - (g n - g n)
    ring
  · have hHn : H ≤ n := by omega
    rw [finiteHead_apply_eq_zero H (f - g) n hHn,
      finiteHead_apply_eq_zero H f n hHn, finiteHead_apply_eq_zero H g n hHn]
    ring

/-- Exact head/tail decomposition of the full signed inner product. -/
theorem inner_eq_headCross_add_tail (H : ℕ) (f g : QHilbert) :
    inner ℝ f g = headCross H f g + inner ℝ (tail H f) (tail H g) := by
  rw [headCross_eq_inner]
  have hz : inner ℝ (f - finiteHead H f) (finiteHead H g) = 0 := by
    rw [real_inner_comm]
    exact inner_finiteHead_tail H g f
  change inner ℝ f g = inner ℝ (finiteHead H f) g +
    inner ℝ (f - finiteHead H f) (g - finiteHead H g)
  rw [inner_sub_right, hz, sub_zero, inner_sub_left]
  ring

/-- Projection orthogonality identifies the cumulative moment with the exact
tail energy difference. The source is `u` and the removed remainder is `u-b`. -/
theorem headCross_eq_tail_energy (H : ℕ) (b u : QHilbert)
    (horth : inner ℝ b (u - b) = 0) :
    headCross H b (u - b) =
      ‖tail H b‖ ^ 2 - inner ℝ (tail H b) (tail H u) := by
  have h := inner_eq_headCross_add_tail H b (u - b)
  rw [horth, tail_sub, inner_sub_right, real_inner_self_eq_norm_sq] at h
  linarith

/-- Completing the square retains the nonnegative remainder exactly. -/
theorem headCross_completed_square (H : ℕ) (b u : QHilbert)
    (horth : inner ℝ b (u - b) = 0) :
    headCross H b (u - b) =
      ‖tail H b - (1 / 2 : ℝ) • tail H u‖ ^ 2 - ‖tail H u‖ ^ 2 / 4 := by
  rw [headCross_eq_tail_energy H b u horth,
    norm_sub_sq_real, inner_smul_right, norm_smul]
  norm_num
  ring

theorem headCross_lower (H : ℕ) (b u : QHilbert)
    (horth : inner ℝ b (u - b) = 0) :
    - ‖tail H u‖ ^ 2 / 4 ≤ headCross H b (u - b) := by
  rw [headCross_completed_square H b u horth]
  nlinarith [sq_nonneg ‖tail H b - (1 / 2 : ℝ) • tail H u‖]

theorem weightedHeadCross_abel (k H : ℕ) (f g : QHilbert) :
    weightedHeadCross k H f g =
      polylogTailProfile k H * headCross H f g -
        ∑ t ∈ Finset.range H,
          (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
            headCross t f g := by
  simpa only [weightedHeadCross, headCross, mul_assoc] using
    RiemannResearch.Analysis.finite_abel (polylogTailProfile k)
      (fun n => positiveQWeight n * qSequence f n * qSequence g n) H

/-- The positive cumulative moments enter Abel summation with a minus sign. -/
def positiveCrossVariation (k H : ℕ) (f g : QHilbert) : ℝ :=
  ∑ t ∈ Finset.range H,
    (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
      max (headCross t f g) 0

theorem weightedHeadCross_lower_of_positive_variation
    (k H : ℕ) (b u : QHilbert) (horth : inner ℝ b (u - b) = 0) :
    - (polylogTailProfile k H * ‖tail H u‖ ^ 2 / 4) -
      positiveCrossVariation k H b (u - b) ≤
        weightedHeadCross k H b (u - b) := by
  have hboundary := mul_le_mul_of_nonneg_left
    (headCross_lower H b u horth) (polylogTailProfile_nonneg k H)
  have hsum :
      (∑ t ∈ Finset.range H,
        (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
          headCross t b (u - b)) ≤ positiveCrossVariation k H b (u - b) := by
    apply Finset.sum_le_sum
    intro t ht
    apply mul_le_mul_of_nonneg_left (le_max_left _ _)
    exact sub_nonneg.mpr (polylogTailProfile_monotone k (Nat.le_succ t))
  rw [weightedHeadCross_abel]
  linarith

end RiemannResearch.RH.QHeadCrossMoments
