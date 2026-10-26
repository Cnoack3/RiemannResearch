/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParityReciprocalBounds
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QShiftedReciprocalTail
import RiemannResearch.RH.QParityConditionalTarget
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# The reciprocal form on the parity annihilator

Source: the user's actual squarefree bound request, 26 October 2026.
Removing physical site two from an odd-orthogonal vector yields the sharp
one-third form bound. The complete nonnegative tail defect is retained.
This does not assert weighted stability of the squarefree projection.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QParityReciprocalBounds
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QShiftedReciprocal QSquarefreeSmoothedProjection

/-- Remove physical site two, which is absent from the parity atom. -/
private def eraseSecond (f : QHilbert) : QHilbert :=
  ⟨fun n => if n = 1 then 0 else f n, by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).mpr
    have hs : Summable (fun n : ℕ => (if n = 1 then 0 else f n) ^ 2) := by
      apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
        (qCoordinate_square_summable f)
      intro n
      split_ifs <;> simp [sq_nonneg]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs⟩

private theorem eraseSecond_norm_sq (f : QHilbert) :
    ‖eraseSecond f‖ ^ 2 = ‖f‖ ^ 2 - (f 1) ^ 2 := by
  have hf := (qCoordinate_square_summable f).sum_add_tsum_nat_add 2
  have he := (qCoordinate_square_summable (eraseSecond f)).sum_add_tsum_nat_add 2
  have ht (n : ℕ) : eraseSecond f (n + 2) = f (n + 2) := by
    change (if n + 2 = 1 then 0 else f (n + 2)) = f (n + 2)
    simp [show n + 2 ≠ 1 by omega]
  simp_rw [ht] at he
  rw [← qNorm_sq] at hf he
  norm_num [Finset.sum_range_succ, eraseSecond] at hf he
  change (f 0) ^ 2 + (∑' i : ℕ, (f (i + 2)) ^ 2) = ‖eraseSecond f‖ ^ 2 at he
  linarith

private theorem eraseSecond_odd_inner (f : QHilbert) :
    inner ℝ (eraseSecond f) ((2 : ℝ) • qResidue 2) =
      inner ℝ f ((2 : ℝ) • qResidue 2) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change (((2 : ℝ) • qResidue 2) n) * eraseSecond f n =
    (((2 : ℝ) • qResidue 2) n) * f n
  by_cases hn : n = 1
  · subst n
    have ho : ((2 : ℝ) • qResidue 2) 1 = 0 := by
      change 2 * (Real.sqrt (qWeight 1) * ArithmeticCumulative.residueFraction 2 2) = 0
      norm_num [ArithmeticCumulative.residueFraction]
    rw [ho]
    simp
  · simp [eraseSecond, hn]

/-- The first coordinate uses at most one third of the energy outside site two. -/
theorem first_coordinate_le_third_off_second (r : QHilbert)
    (hr : inner ℝ r ((2 : ℝ) • qResidue 2) = 0) :
    3 * (r 0) ^ 2 ≤ ‖r‖ ^ 2 - (r 1) ^ 2 := by
  let w := eraseSecond r
  have hwodd : inner ℝ w ((2 : ℝ) • qResidue 2) = 0 := by
    rw [eraseSecond_odd_inner, hr]
  have hf := first_sq_le_of_odd_orthogonal w hwodd
  have hx : zetaTwo * (r 0) ^ 2 = (qSequence w 1) ^ 2 := by
    have he := qSequence_weighted_square w 0
    norm_num only [positiveQWeight, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
      zero_add, one_pow, mul_one] at he
    have hw0 : w 0 = r 0 := by simp [w, eraseSecond]
    rw [hw0] at he
    calc
      _ = zetaTwo * ((1 / zetaTwo) * (qSequence w 1) ^ 2) := by rw [he]
      _ = _ := by field_simp [ne_of_gt zetaTwo_pos]
  have hw : ‖w‖ ^ 2 = ‖r‖ ^ 2 - (r 1) ^ 2 := eraseSecond_norm_sq r
  have hxle : (r 0) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [qNorm_sq]
    have hs := (qCoordinate_square_summable w).sum_le_tsum ({0} : Finset ℕ)
      (fun n _ => sq_nonneg (w n))
    simpa [w, eraseSecond] using hs
  have hz : zetaTwo ≤ 2 := by
    linarith [QFiniteEnergyBounds.zetaTwo_rational_bounds.2]
  have hprod := mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hxle)
  rw [← hx] at hf
  rw [hw] at hf hxle hprod
  nlinarith

/-- The complete B form contracts by one third on the parity-annihilator space.
This is sharp on that whole space: the vector supported at physical site two
has B eigenvalue one third and is orthogonal to the parity atom. -/
theorem B_inner_le_third_of_odd_orthogonal (r : QHilbert)
    (hr : inner ℝ r ((2 : ℝ) • qResidue 2) = 0) :
    inner ℝ r (B r) ≤ ‖r‖ ^ 2 / 3 := by
  have hsplit := B_inner_le_two_coordinate_split r
  have hfirst := first_coordinate_le_third_off_second r hr
  linarith

/-- The sharper form keeps the named complete tail on the left. -/
theorem B_inner_add_tailDefect_le_third_of_odd_orthogonal (r : QHilbert)
    (hr : inner ℝ r ((2 : ℝ) • qResidue 2) = 0) :
    inner ℝ r (B r) + B_twoCoordinate_tailDefect r ≤ ‖r‖ ^ 2 / 3 := by
  have he := B_inner_two_coordinate_exact r
  have hfirst := first_coordinate_le_third_off_second r hr
  linarith

theorem residual_B_inner_le_third (N : ℕ) (hN : 0 < N) :
    inner ℝ (residual N) (B (residual N)) ≤ error N / 3 := by
  obtain ⟨hodd, _⟩ := projectionResidual_parity_moments (stage N)
    (QParityConditionalTarget.qResidue_two_mem_stage N hN)
  exact B_inner_le_third_of_odd_orthogonal (residual N) hodd

theorem residual_B_inner_add_tailDefect_le_third (N : ℕ) (hN : 0 < N) :
    inner ℝ (residual N) (B (residual N)) +
      B_twoCoordinate_tailDefect (residual N) ≤ error N / 3 := by
  obtain ⟨hodd, _⟩ := projectionResidual_parity_moments (stage N)
    (QParityConditionalTarget.qResidue_two_mem_stage N hN)
  exact B_inner_add_tailDefect_le_third_of_odd_orthogonal (residual N) hodd

end RiemannResearch.RH.QParityReciprocalBounds
