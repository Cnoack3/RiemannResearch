/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoExactHeadPairings
import RiemannResearch.RH.QQuantitativeExactHeadAverages
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual online legal approximation in the complete Q norm

Source: constructive approximants handoff, 24 October 2026, Sections 8 and 10.
The executable integer selector and complete-P tail estimate are assembled
with the exact P-to-Q metric comparison. No Q-pairing hypothesis is supplied:
the physical amplitude bounds and exact heads supply the required pairings.
The uniform complete-P residual bound remains an explicit arithmetic input.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QExactHeadAverages

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open RiemannResearch.Analysis

private theorem residual_sequence_pos (f : QHilbert) {n : ℕ} (hn : 0 < n) :
    qSequence (qOne - f) n = 1 - qSequence f n := by
  change qSequenceLinear (qOne - f) n = _
  rw [map_sub]
  change qSequence qOne n - qSequence f n = _
  simp only [qSequence_qOne, qOneSequence, if_neg (Nat.ne_of_gt hn)]

/-- The complete Pareto estimate for the actual Q block with the same
physical coefficients. The selection uses U alone and is fully explicit. -/
theorem online_block_pareto_error_le
    (F : ℕ → QHilbert) (U : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N, ‖toPareto (qOne - F N)‖ ^ 2 ≤ C ^ 2)
    (hphysical : ∀ N n, 0 < n → |1 - qSequence (F N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → qSequence (F N) n = 1)
    {m : ℕ} (hm : 0 < m) :
    ‖toPareto (qOne - blockAverage F (exactHeadSelection U) m)‖ ^ 2 ≤
      C ^ 2 / m + 2 * C * (1 / 2 : ℝ) ^ m / (m : ℝ) ^ 2 := by
  have hp : ∀ N n, 0 < n →
      |Pareto.hilbertSequence (toPareto (qOne - F N)) n| ≤ (U N : ℝ) := by
    intro N n hn
    rw [toPareto_sequence, residual_sequence_pos _ hn]
    exact hphysical N n hn
  have hh : ∀ N n, 0 < n → n ≤ N →
      Pareto.hilbertSequence (toPareto (qOne - F N)) n = 0 := by
    intro N n hn hnN
    rw [toPareto_sequence, residual_sequence_pos _ hn, hhead N n hn hnN, sub_self]
  have he : toPareto (qOne - blockAverage F (exactHeadSelection U) m) =
      ((m : ℝ)⁻¹) • ∑ i ∈ Finset.range m,
        toPareto (qOne - F (exactHeadSelection U (m + i))) := by
    change toParetoLinear
      (qOne - average F (fun i => exactHeadSelection U (m + i)) m) = _
    rw [residual_average F (fun i => exactHeadSelection U (m + i)) hm,
      map_smul, map_sum]
    rfl
  rw [he]
  exact Pareto.online_exact_head_block_average_bound
    (fun N => toPareto (qOne - F N)) U C hC hbound hp hh m hm

/-- The complete Q error has the sharp head-dependent metric factor.
Every mixed term was retained before the preceding Pareto bound was applied. -/
theorem online_block_q_error_le_sharp
    (F : ℕ → QHilbert) (U : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N, ‖toPareto (qOne - F N)‖ ^ 2 ≤ C ^ 2)
    (hphysical : ∀ N n, 0 < n → |1 - qSequence (F N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → qSequence (F N) n = 1)
    {m : ℕ} (hm : 0 < m) :
    zetaTwo * ‖qOne - blockAverage F (exactHeadSelection U) m‖ ^ 2 ≤
      (1 + 1 / ((exactHeadSelection U m : ℝ) + 1)) *
        (C ^ 2 / m + 2 * C * (1 / 2 : ℝ) ^ m / (m : ℝ) ^ 2) := by
  have hh : ∀ n, 0 < n → n ≤ exactHeadSelection U m →
      qSequence (qOne - blockAverage F (exactHeadSelection U) m) n = 0 := by
    intro n hn hnN
    rw [residual_sequence_pos _ hn,
      blockAverage_head_through_first F (exactHeadSelection U)
        (exactHeadSelection_strictMono U).monotone hhead hm hn hnN, sub_self]
  exact (QParetoMetric.norm_sq_le_of_head_zero
    (qOne - blockAverage F (exactHeadSelection U) m) (exactHeadSelection U m) hh).trans
      (mul_le_mul_of_nonneg_left
        (online_block_pareto_error_le F U C hC hbound hphysical hhead hm) (by positivity))

/-- A simpler complete-Q bound suited to a finite stopping tolerance. -/
theorem online_block_q_error_le
    (F : ℕ → QHilbert) (U : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N, ‖toPareto (qOne - F N)‖ ^ 2 ≤ C ^ 2)
    (hphysical : ∀ N n, 0 < n → |1 - qSequence (F N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → qSequence (F N) n = 1)
    {m : ℕ} (hm : 0 < m) :
    ‖qOne - blockAverage F (exactHeadSelection U) m‖ ^ 2 ≤
      (2 / zetaTwo) * (C ^ 2 / m + 2 * C / (m : ℝ) ^ 2) := by
  have hfactor : 1 + 1 / ((exactHeadSelection U m : ℝ) + 1) ≤ 2 := by
    have hi : 1 / ((exactHeadSelection U m : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [show (0 : ℝ) ≤ (exactHeadSelection U m : ℝ) from Nat.cast_nonneg _]
    linarith
  have hb : C ^ 2 / m + 2 * C * (1 / 2 : ℝ) ^ m / (m : ℝ) ^ 2 ≤
      C ^ 2 / m + 2 * C / (m : ℝ) ^ 2 := by
    apply add_le_add_right
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1))
      (mul_nonneg (by norm_num) hC)
  have hs : zetaTwo * ‖qOne - blockAverage F (exactHeadSelection U) m‖ ^ 2 ≤
      2 * (C ^ 2 / m + 2 * C / (m : ℝ) ^ 2) := by
    apply (online_block_q_error_le_sharp F U C hC hbound hphysical hhead hm).trans
    exact (mul_le_mul_of_nonneg_right hfactor (by positivity)).trans
      (mul_le_mul_of_nonneg_left hb (by norm_num))
  calc
    _ ≤ (2 * (C ^ 2 / m + 2 * C / (m : ℝ) ^ 2)) / zetaTwo := by
      apply (le_div_iff₀ zetaTwo_pos).mpr
      simpa only [mul_comm] using hs
    _ = _ := by ring

/-- Explicit finite tolerance for the constructed block. Only the numerical
certificate C enters this stopping rule; the head selector itself ignores C. -/
theorem online_block_error_lt_of_tolerance
    (F : ℕ → QHilbert) (U : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N, ‖toPareto (qOne - F N)‖ ^ 2 ≤ C ^ 2)
    (hphysical : ∀ N n, 0 < n → |1 - qSequence (F N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → qSequence (F N) n = 1)
    {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 0 < m)
    (hstop : (2 * (C ^ 2 + 2 * C) / zetaTwo) / ε ^ 2 < (m : ℝ)) :
    ‖qOne - blockAverage F (exactHeadSelection U) m‖ < ε := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsmall : 2 * C / (m : ℝ) ^ 2 ≤ 2 * C / (m : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hmR (by nlinarith)
  have hs : ‖qOne - blockAverage F (exactHeadSelection U) m‖ ^ 2 ≤
      (2 * (C ^ 2 + 2 * C) / zetaTwo) / m := by
    apply (online_block_q_error_le F U C hC hbound hphysical hhead hm).trans
    calc
      _ ≤ (2 / zetaTwo) * (C ^ 2 / m + 2 * C / m) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hsmall _)
          (div_nonneg (by norm_num) (le_of_lt zetaTwo_pos))
      _ = _ := by ring
  have hs' : (2 * (C ^ 2 + 2 * C) / zetaTwo) / m < ε ^ 2 := by
    apply (div_lt_iff₀ hmR).mpr
    have hh := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hstop
    nlinarith
  nlinarith [norm_nonneg (qOne - blockAverage F (exactHeadSelection U) m)]

/-- Strong convergence for the actual executable online selection. This is
conditional on the complete-P bound, not on any supplied small pairings. -/
theorem online_block_tendsto
    (F : ℕ → QHilbert) (U : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N, ‖toPareto (qOne - F N)‖ ^ 2 ≤ C ^ 2)
    (hphysical : ∀ N n, 0 < n → |1 - qSequence (F N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → qSequence (F N) n = 1) :
    Tendsto (blockAverage F (exactHeadSelection U)) atTop (𝓝 qOne) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hm : ∀ᶠ m : ℕ in atTop, 0 < m := eventually_gt_atTop 0
  have hs : ∀ᶠ m : ℕ in atTop,
      (2 * (C ^ 2 + 2 * C) / zetaTwo) / ε ^ 2 < (m : ℝ) :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).eventually
        (eventually_gt_atTop _)
  filter_upwards [hm, hs] with m hm hs
  rw [dist_eq_norm, norm_sub_rev]
  exact online_block_error_lt_of_tolerance F U C hC hbound hphysical hhead hε hm hs

/-- The displayed sequence is legal at every stage, preserves growing exact
heads, and converges strongly to the actual constant target. -/
theorem online_legal_blocks
    (S : Submodule ℝ QHilbert) (F : ℕ → QHilbert) (U : ℕ → ℕ)
    (C : ℝ) (hC : 0 ≤ C) (hlegal : ∀ N, F N ∈ S)
    (hbound : ∀ N, ‖toPareto (qOne - F N)‖ ^ 2 ≤ C ^ 2)
    (hphysical : ∀ N n, 0 < n → |1 - qSequence (F N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → qSequence (F N) n = 1) :
    (∀ m, blockAverage F (exactHeadSelection U) m ∈ S) ∧
      (∀ m n, 0 < m → 0 < n → n ≤ exactHeadSelection U m →
        qSequence (blockAverage F (exactHeadSelection U) m) n = 1) ∧
      Tendsto (blockAverage F (exactHeadSelection U)) atTop (𝓝 qOne) := by
  exact ⟨blockAverage_mem S F (exactHeadSelection U) hlegal,
    fun m n hm hn hnN => blockAverage_head_through_first F (exactHeadSelection U)
      (exactHeadSelection_strictMono U).monotone hhead hm hn hnN,
    online_block_tendsto F U C hC hbound hphysical hhead⟩

end RiemannResearch.RH.QExactHeadAverages
