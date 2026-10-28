/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeResponsePrefixBudget
import RiemannResearch.RH.QParitySmoothingEnergy
import RiemannResearch.RH.QSquarefreeResponseSeries
import RiemannResearch.RH.QCanonicalInnovation
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QShiftedReciprocalBessel
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A strict second initial response-budget improvement

Source: the user-requested exact initial-innovation investigation, 2026-10-28.
The conductor-three atom has positive pairing with the actual parity residual.
Both initial directions vanish at physical site six, leaving at least 1/49
of the complete diagonal smoothing trace unused by the two-direction prefix.
The second response cost is retained in `responsePrefixBudget 2`.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage ZetaTwoParitySignal
open QShiftedReciprocal QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.ExhaustiveWalk

theorem qResidue_three_mem_stage_two : qResidue 3 ∈ stage 2 := by
  change qResidue 3 ∈ Submodule.span ℝ
    (Set.range (fun i : Fin 2 => squarefreeAtom (id i)))
  apply Submodule.subset_span
  refine ⟨⟨1, by decide⟩, ?_⟩
  norm_num [squarefreeAtom, Nat.prime_three.squarefree]

/-- The next actual projection changes: parity has not exhausted the target. -/
theorem optimizer_two_sub_one_ne_zero : optimizer 2 - optimizer 1 ≠ 0 := by
  intro hz
  have he : optimizer 2 = optimizer 1 := sub_eq_zero.mp hz
  have hr : residual 2 = residual 1 := by
    simp only [ZetaTwoOptimizerStage.residual, he]
  have ho := Submodule.inner_right_of_mem_orthogonal
    qResidue_three_mem_stage_two (residual_mem_orthogonal 2)
  rw [hr, residual_one, real_inner_comm] at ho
  exact (ne_of_gt qEven_inner_qResidue_three_pos) ho

/-- Strict residual improvement at conductor three, without a special-function
evaluation of its Gram matrix. -/
theorem error_two_lt_one : error 2 < error 1 := by
  have he := walkError_step squarefreeAtom id qOne 1
  change error 1 = error 2 + ‖optimizer 2 - optimizer 1‖ ^ 2 at he
  have hp : 0 < ‖optimizer 2 - optimizer 1‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr optimizer_two_sub_one_ne_zero)
  linarith

theorem error_two_lt_quarter : error 2 < (1 / 4 : ℝ) := by
  simpa only [error_one] using error_two_lt_one

/-- Normalized coordinate five is physical site six, a common zero of g2,g3. -/
theorem stage_two_coordinate_five_eq_zero (v : QHilbert) (hv : v ∈ stage 2) :
    v 5 = 0 := by
  unfold stage walkSpan at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      fin_cases i <;>
        norm_num [squarefreeAtom, Nat.prime_two.squarefree,
          Nat.prime_three.squarefree, qResidue, encodeQ,
          RiemannResearch.RH.ArithmeticCumulative.residueFraction]
  | zero => rfl
  | add y z hy hz hiy hiz =>
      change y 5 + z 5 = 0
      rw [hiy, hiz]
      ring
  | smul c y hy hiy =>
      change c * y 5 = 0
      rw [hiy]
      ring

theorem direction_zero_coordinate_five : direction 0 5 = 0 := by
  apply stage_two_coordinate_five_eq_zero
  exact (walkSpan_mono squarefreeAtom id (by decide : 1 ≤ 2)) (direction_mem_succ 0)

theorem direction_one_coordinate_five : direction 1 5 = 0 :=
  stage_two_coordinate_five_eq_zero _ (direction_mem_succ 1)

private theorem direction_pair_coordinate_sq_le (n : ℕ) :
    (direction 0 n) ^ 2 + (direction 1 n) ^ 2 ≤ 1 := by
  classical
  have h := orthonormal_coordinate_square_sum_le_one
    (fun i : Active => direction i) active_orthonormal
    ((Finset.range 2).subtype (fun j => direction j ≠ 0)) n
  have he (j : ℕ) :
      (if direction j ≠ 0 then (direction j n) ^ 2 else 0) =
        (direction j n) ^ 2 := by
    by_cases hj : direction j = 0 <;> simp [hj]
  have hs := Finset.sum_subtype_eq_sum_filter
    (s := Finset.range 2) (p := fun j => direction j ≠ 0)
    (fun j : ℕ => (direction j n) ^ 2)
  have hf : (∑ j ∈ Finset.range 2 with direction j ≠ 0,
      (direction j n) ^ 2) ≤ 1 := hs.symm.trans_le h
  simpa [Finset.sum_filter, he, Finset.sum_range_succ] using hf

/-- Complete trace deficit after the first two innovations. The proof sums
the nonnegative coordinate deficits over every physical site, retaining the
single known deficit at physical site six. -/
theorem smoothing_prefix_two_complement_ge :
    (1 / 49 : ℝ) ≤ zetaTwo - 1 -
      ∑ j ∈ Finset.range 2, ‖B (direction j)‖ ^ 2 := by
  classical
  let f : ℕ → ℝ := fun n =>
    (B (direction 0) n) ^ 2 + (B (direction 1) n) ^ 2
  let g : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) ^ 2
  have hf : Summable f :=
    (qCoordinate_square_summable (B (direction 0))).add
      (qCoordinate_square_summable (B (direction 1)))
  have hg : Summable g := shifted_reciprocal_square_summable
  have hbound (n : ℕ) : f n ≤ g n := by
    dsimp only [f, g]
    simp only [B_apply, div_pow]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (direction_pair_coordinate_sq_le n)
      (sq_nonneg _)
  have hsum := Summable.sum_le_tsum ({5} : Finset ℕ)
    (fun n _ => sub_nonneg.mpr (hbound n)) (hg.sub hf)
  have hzero : f 5 = 0 := by
    dsimp only [f]
    rw [B_apply, B_apply, direction_zero_coordinate_five,
      direction_one_coordinate_five]
    norm_num
  have he : (∑' n, (g n - f n)) = zetaTwo - 1 -
      (‖B (direction 0)‖ ^ 2 + ‖B (direction 1)‖ ^ 2) := by
    rw [hg.tsum_sub hf]
    dsimp only [g, f]
    rw [shifted_reciprocal_square_tsum,
      (qCoordinate_square_summable (B (direction 0))).tsum_add
        (qCoordinate_square_summable (B (direction 1))),
      ← qNorm_sq, ← qNorm_sq]
  rw [Finset.sum_singleton, hzero, sub_zero, he] at hsum
  norm_num only [g, Nat.cast_ofNat] at hsum
  simpa [Finset.sum_range_succ] using hsum

theorem smoothing_prefix_two_lt_trace :
    (∑ j ∈ Finset.range 2, ‖B (direction j)‖ ^ 2) < zetaTwo - 1 := by
  have h := smoothing_prefix_two_complement_ge
  linarith

/-- The conductor-three refinement is strict, and includes its actual response
cost rather than deleting that cost from the global variation. -/
theorem responsePrefixBudget_two_lt_one :
    responsePrefixBudget 2 < responsePrefixBudget 1 :=
  responsePrefixBudget_succ_lt_of_error_lt 1 error_two_lt_one
    smoothing_prefix_two_lt_trace

/-- A quantitative portion of the strict improvement is already controlled
without evaluating the conductor-three smoothing constants. -/
theorem responsePrefixBudget_one_sub_two_ge :
    (error 1 - error 2) / 49 ≤ responsePrefixBudget 1 - responsePrefixBudget 2 := by
  have hE : 0 ≤ error 1 - error 2 := (sub_pos.mpr error_two_lt_one).le
  have hm := mul_le_mul_of_nonneg_left smoothing_prefix_two_complement_ge hE
  have hstep := movingCorrection_increment_norm_sq_le 1
  have he := responsePrefixBudget_decrement_exact 1
  nlinarith

/-- Exact form of the improved cap: the non-parity response is charged in full. -/
theorem responsePrefixBudget_two_eq :
    responsePrefixBudget 2 = ‖movingCorrection 2‖ ^ 2 + error 2 *
      (zetaTwo - 1 - ‖B (direction 0)‖ ^ 2 - ‖B (direction 1)‖ ^ 2) := by
  simp only [responsePrefixBudget, Finset.sum_range_succ, Finset.sum_range_zero,
    movingCorrection_zero, movingCorrection_one, sub_zero, norm_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, add_zero]
  ring

theorem movingCorrection_variation_lt_parity_budget :
    (∑' n, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) <
      (zetaTwo - 1 - ‖B (direction 0)‖ ^ 2) / 4 := by
  have h := (movingCorrection_variation_prefix_le 2).trans_lt
    responsePrefixBudget_two_lt_one
  simpa only [responsePrefixBudget_one] using h

/-- The exact arithmetic parity cap is already strictly improvable. -/
theorem movingCorrection_variation_lt_explicit_parity :
    (∑' n, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) <
      (zetaTwo - 1 -
        4 * (zetaTwo - 2 * Real.log 2) / (3 * zetaTwo)) / 4 := by
  simpa only [B_direction_zero_norm_sq] using movingCorrection_variation_lt_parity_budget

end RiemannResearch.RH.QCanonicalInnovation
