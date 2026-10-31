/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoMobiusQuarticFloor
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete Q error of the raw squarefree Mobius trial

Source: the user's 30 October 2026 request to test explicit alternative
coefficients. The existing finite head identity is summed with the actual
Q weights. Every tail term remains in the primary equality. The classical
oscillation provider, discussed in the companion research memorandum using
Baez-Duarte, arXiv:math/0011254, Lemma 2.1 and Proposition 2.1, is not
asserted by the conditional nonconvergence declaration below.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QMobiusTrialHeadObstruction
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open Pareto (mobiusReciprocalSum)

/-- Exact contribution of the physical coordinates 1,...,N+1. -/
theorem head_energy (N : ℕ) :
    (∑ k ∈ Finset.range (N + 2), positiveQWeight k *
      (qSequence (qOne - mobiusTrial N) k)^2) =
        ((N + 1 : ℕ) : ℝ) / zetaTwo * (mobiusReciprocalSum (N + 1))^2 := by
  rw [Finset.sum_range_succ']
  simp only [qSequence_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
      positiveQWeight (k + 1) * (qSequence (qOne - mobiusTrial N) (k + 1))^2 =
        (mobiusReciprocalSum (N + 1))^2 / zetaTwo := by
    rw [qSequence_mobiusResidual N (k + 1) (by omega),
      Pareto.ZetaTwoMobiusFloor.residual_head (N + 1) (k + 1)
        (by omega) (by have := Finset.mem_range.mp hk; omega)]
    unfold positiveQWeight
    have hk0 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hk0]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The entire signed-tail difficulty is retained as a nonnegative norm tail. -/
theorem error_head_tail (N : ℕ) :
    ‖qOne - mobiusTrial N‖^2 =
      ((N + 1 : ℕ) : ℝ) / zetaTwo * (mobiusReciprocalSum (N + 1))^2 +
      ∑' j : ℕ, positiveQWeight (j + (N + 2)) *
        (qSequence (qOne - mobiusTrial N) (j + (N + 2)))^2 := by
  rw [qNorm_weighted_sq,
    ← Summable.sum_add_tsum_nat_add (N + 2)
      (qSequence_square_summable (qOne - mobiusTrial N)), head_energy]

theorem head_energy_le_error (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) / zetaTwo * (mobiusReciprocalSum (N + 1))^2 ≤
      ‖qOne - mobiusTrial N‖^2 := by
  rw [error_head_tail]
  apply le_add_of_nonneg_right
  exact tsum_nonneg (fun j => mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))

/-- Conditional obstruction: the classical arithmetic nonzero-limsup provider
is explicit and is not confused with a lower bound for the canonical optimizer. -/
theorem not_tendsto_error_zero_of_head
    (h : ¬ Tendsto (fun N => ((N + 1 : ℕ) : ℝ) / zetaTwo *
      (mobiusReciprocalSum (N + 1))^2) atTop (𝓝 0)) :
    ¬ Tendsto (fun N => ‖qOne - mobiusTrial N‖^2) atTop (𝓝 0) := by
  intro he
  apply h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
  · intro N
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) zetaTwo_pos.le) (sq_nonneg _)
  · exact head_energy_le_error

end RiemannResearch.RH.QMobiusTrialHeadObstruction
