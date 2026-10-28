/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeResponseSeries
import RiemannResearch.RH.QCanonicalInnovation
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact finite-prefix accounting for the complete variation budget

Source: user-requested continuation of InfiniteSquarefreeResponseResearch20261027.md.
Every initial response cost is retained. Only the complete remaining infinite
variation is bounded using the actual residual at the end of the prefix.
The prefix contains stage indices, never a truncation of physical coordinates.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.ExhaustiveWalk

/-- The exact measured prefix plus an upper bound on the complete remaining tail. -/
def responsePrefixBudget (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) +
    error N * (zetaTwo - 1 - ∑ n ∈ Finset.range N, ‖B (direction n)‖ ^ 2)

/-- An exact infinite decomposition precedes the tail estimate. -/
theorem movingCorrection_variation_prefix_exact (N : ℕ) :
    (∑' n, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) =
      (∑ n ∈ Finset.range N, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) +
      ∑' j, ‖movingCorrection (j + N + 1) - movingCorrection (j + N)‖ ^ 2 := by
  exact (Summable.sum_add_tsum_nat_add N movingCorrection_variation.1).symm

/-- Exact accounting: the remaining trace cap equals its unused total mass
plus the complete smoothing-energy tail. -/
theorem smoothing_prefix_complement_exact (N : ℕ) :
    zetaTwo - 1 - ∑ n ∈ Finset.range N, ‖B (direction n)‖ ^ 2 =
      (zetaTwo - 1 - ∑' n, ‖B (direction n)‖ ^ 2) + smoothingTail N := by
  have h := Summable.sum_add_tsum_nat_add N B_direction_sq_summable
  dsimp only [smoothingTail]
  linarith

theorem smoothingTail_le_prefix_complement (N : ℕ) :
    smoothingTail N ≤
      zetaTwo - 1 - ∑ n ∈ Finset.range N, ‖B (direction n)‖ ^ 2 := by
  rw [smoothing_prefix_complement_exact]
  linarith [B_direction_tsum_le]

/-- Later innovations may be removed from the smoothing tail only after their
actual response costs have been included in the finite prefix. -/
theorem movingCorrection_variation_prefix_le (N : ℕ) :
    (∑' n, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) ≤
      responsePrefixBudget N := by
  have htail := movingCorrection_variation_tail_le N
  have hmul := mul_le_mul_of_nonneg_left
    (smoothingTail_le_prefix_complement N) (show 0 ≤ error N from sq_nonneg _)
  rw [movingCorrection_variation_prefix_exact N]
  unfold responsePrefixBudget
  exact add_le_add le_rfl (htail.trans hmul)

/-- The exact change of the numerical cap retains both nonnegative gains. -/
theorem responsePrefixBudget_decrement_exact (N : ℕ) :
    responsePrefixBudget N - responsePrefixBudget (N + 1) =
      (error N * ‖B (direction N)‖ ^ 2 -
        ‖movingCorrection (N + 1) - movingCorrection N‖ ^ 2) +
      (error N - error (N + 1)) *
        (zetaTwo - 1 - ∑ n ∈ Finset.range (N + 1), ‖B (direction n)‖ ^ 2) := by
  simp only [responsePrefixBudget, Finset.sum_range_succ]
  ring

theorem responsePrefixBudget_succ_le (N : ℕ) :
    responsePrefixBudget (N + 1) ≤ responsePrefixBudget N := by
  have hstep := movingCorrection_increment_norm_sq_le N
  have hE : error (N + 1) ≤ error N :=
    walkError_antitone squarefreeAtom id qOne (Nat.le_succ N)
  have htrace : 0 ≤ zetaTwo - 1 -
      ∑ n ∈ Finset.range (N + 1), ‖B (direction n)‖ ^ 2 :=
    sub_nonneg.mpr (B_direction_finite_budget (Finset.range (N + 1)))
  have hprod := mul_nonneg (sub_nonneg.mpr hE) htrace
  have he := responsePrefixBudget_decrement_exact N
  linarith

/-- A strict residual improvement gives a strict cap improvement whenever
there is still unused trace mass. Both hypotheses are explicit. -/
theorem responsePrefixBudget_succ_lt_of_error_lt (N : ℕ)
    (hE : error (N + 1) < error N)
    (htrace : (∑ n ∈ Finset.range (N + 1), ‖B (direction n)‖ ^ 2) < zetaTwo - 1) :
    responsePrefixBudget (N + 1) < responsePrefixBudget N := by
  have hprod := mul_pos (sub_pos.mpr hE) (sub_pos.mpr htrace)
  have hstep := movingCorrection_increment_norm_sq_le N
  have he := responsePrefixBudget_decrement_exact N
  linarith

/-- The one-term prefix is exactly the previously established parity cap. -/
theorem responsePrefixBudget_one :
    responsePrefixBudget 1 = (zetaTwo - 1 - ‖B (direction 0)‖ ^ 2) / 4 := by
  simp only [responsePrefixBudget, Finset.sum_range_one,
    movingCorrection_one, movingCorrection_zero, sub_zero, norm_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, error_one]
  ring

/-- Exact limit of the sequence of caps. This retains the possible positive
limiting residual energy multiplied by unused smoothing mass. -/
theorem responsePrefixBudget_tendsto :
    Tendsto responsePrefixBudget atTop
      (𝓝 ((∑' n, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) +
        ‖limitingResidual‖ ^ 2 *
          (zetaTwo - 1 - ∑' n, ‖B (direction n)‖ ^ 2))) := by
  have hE : Tendsto error atTop (𝓝 (‖limitingResidual‖ ^ 2)) := by
    change Tendsto (fun N => ‖ZetaTwoOptimizerStage.residual N‖ ^ 2) atTop _
    exact residual_tendsto.norm.pow 2
  have htrace : Tendsto
      (fun N : ℕ => zetaTwo - 1 - ∑ n ∈ Finset.range N, ‖B (direction n)‖ ^ 2)
      atTop (𝓝 (zetaTwo - 1 - ∑' n, ‖B (direction n)‖ ^ 2)) :=
    tendsto_const_nhds.sub B_direction_sq_summable.hasSum.tendsto_sum_nat
  exact movingCorrection_variation.1.hasSum.tendsto_sum_nat.add (hE.mul htrace)

end RiemannResearch.RH.QCanonicalInnovation
