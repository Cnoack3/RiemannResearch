/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeMeasureRigidity
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QScaledTailPerturbation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded displacement forces squarefree projection agreement

Source: the user's measure-change agenda, 25 October 2026.
All projections use the same closed physical squarefree span.
For d = f_Q - f_P and r_P in Q coordinates, u = B r_P - d is a
squarefree annihilator and
  zeta(2) * <1,u>_Q = zeta(2) * <r_Q,B r_Q>_Q + ||T d||_P^2.
Both nonnegative terms are retained. Bounded d forces this mean to
vanish, hence r_Q = 0. A nonzero r_Q forces divergent scaled tails of d.

Physical boundedness, or a cofinal scaled-tail bound, is an OPEN arithmetic
premise in the RH corollaries. The module does not prove either bound.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QParetoClosedProjectionComparison
open QSquarefreeMeasureRigidity QShiftedReciprocal QSquarefreeResidualTail
open ZetaTwoOptimizerStage QAnnihilatorTailEscape QFiniteSupportDualCriterion

/-- Pareto residual represented in physical Q coordinates. -/
def pResidual : QHilbert := qOne - pFit paretoSquarefreeClosure qOne

/-- Q projection minus Pareto projection, in the same physical realization. -/
def displacement : QHilbert :=
  closure.starProjection qOne - pFit paretoSquarefreeClosure qOne

theorem pResidual_eq_residual_add_displacement :
    pResidual = limitingResidual + displacement := by
  change qOne - pFit paretoSquarefreeClosure qOne =
    (qOne - closure.starProjection qOne) +
      (closure.starProjection qOne - pFit paretoSquarefreeClosure qOne)
  abel

theorem displacement_mem : displacement ∈ closure := by
  exact closure.sub_mem (closure.starProjection_apply_mem qOne)
    (pFit_mem closure paretoSquarefreeClosure
      toPareto_mem_paretoSquarefreeClosure_iff qOne)

def witness : QHilbert := B pResidual - displacement

theorem witness_mem_orthogonal : witness ∈ closureᗮ := by
  apply (closure.mem_orthogonal _).mpr
  intro v hv
  have hp : inner ℝ (toPareto v) (toPareto pResidual) = 0 := by
    unfold pResidual
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.inner_right_of_mem_orthogonal
      (toPareto_mem_paretoSquarefreeClosure v hv)
      (Submodule.sub_starProjection_mem_orthogonal
        (K := paretoSquarefreeClosure) (toPareto qOne))
  rw [pareto_inner_identity] at hp
  have hp' : inner ℝ v pResidual - inner ℝ v (B pResidual) = 0 :=
    (mul_eq_zero.mp hp).resolve_left (ne_of_gt zetaTwo_pos)
  have hq := Submodule.inner_right_of_mem_orthogonal hv
    limitingResidual_mem_squarefree_orthogonal
  rw [pResidual_eq_residual_add_displacement, inner_add_right, hq,
    zero_add] at hp'
  change inner ℝ v (B pResidual - displacement) = 0
  rw [inner_sub_right, pResidual_eq_residual_add_displacement]
  linarith

/-- A nonzero residual gives this bounded-perturbation annihilator positive mean. -/
theorem witness_mean_energy :
    zetaTwo * inner ℝ qOne witness =
      zetaTwo * inner ℝ limitingResidual (B limitingResidual) +
        ‖toPareto displacement‖ ^ 2 := by
  have hfw := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem qOne) witness_mem_orthogonal
  have hrd : inner ℝ limitingResidual displacement = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal displacement_mem
      limitingResidual_mem_squarefree_orthogonal
  have hmean : inner ℝ qOne witness =
      inner ℝ limitingResidual (B limitingResidual) +
        inner ℝ limitingResidual (B displacement) := by
    calc
      _ = inner ℝ limitingResidual witness := by
        change inner ℝ qOne witness =
          inner ℝ (qOne - closure.starProjection qOne) witness
        rw [inner_sub_left, hfw, sub_zero]
      _ = _ := by
        rw [witness, inner_sub_right, hrd, sub_zero,
          pResidual_eq_residual_add_displacement, map_add, inner_add_right]
  have hcross := Submodule.inner_right_of_mem_orthogonal displacement_mem
    witness_mem_orthogonal
  rw [witness, inner_sub_right, pResidual_eq_residual_add_displacement,
    map_add, inner_add_right, real_inner_self_eq_norm_sq] at hcross
  have hsym : inner ℝ limitingResidual (B displacement) =
      inner ℝ displacement (B limitingResidual) := by
    rw [← B_symmetric, real_inner_comm]
  have hmetric := pareto_inner_identity displacement displacement
  simp only [real_inner_self_eq_norm_sq] at hmetric
  have hc : inner ℝ displacement (B limitingResidual) =
      ‖displacement‖ ^ 2 - inner ℝ displacement (B displacement) := by linarith
  rw [hmean, hsym, hc, hmetric]
  ring

theorem residual_eq_zero_of_witness_mean_zero (hm : inner ℝ qOne witness = 0) :
    limitingResidual = 0 := by
  have he := witness_mean_energy
  rw [hm, mul_zero] at he
  have hp := B_positive limitingResidual
  have hz : zetaTwo * inner ℝ limitingResidual (B limitingResidual) = 0 := by
    nlinarith [mul_nonneg zetaTwo_pos.le hp, sq_nonneg ‖toPareto displacement‖]
  exact B_faithful limitingResidual
    ((mul_eq_zero.mp hz).resolve_left (ne_of_gt zetaTwo_pos))

theorem residual_eq_zero_of_displacement_physically_bounded
    (C : ℝ) (hb : ∀ k : ℕ, |qSequence displacement k| ≤ C) :
    limitingResidual = 0 := by
  obtain ⟨D, hD⟩ := B_physical_bounded pResidual
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb 0)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hw : ∀ k : ℕ, |qSequence witness k| ≤ D + C := by
    intro k
    have he : qSequence witness k =
        qSequence (B pResidual) k - qSequence displacement k := by
      change qSequenceLinear (B pResidual - displacement) k = _
      rw [map_sub]
      rfl
    rw [he]
    calc
      _ ≤ |qSequence (B pResidual) k| + |qSequence displacement k| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (qSequence (B pResidual) k) (-qSequence displacement k)
      _ ≤ D + C := add_le_add (hD k) (hb k)
  have hm := bounded_annihilator_mean_eq_zero witness witness_mem_orthogonal
    (D + C) (add_nonneg hD0 hC0) hw
  exact residual_eq_zero_of_witness_mean_zero hm

theorem displacement_eq_zero_of_residual_eq_zero (hr : limitingResidual = 0) :
    displacement = 0 := by
  have ha := projections_agree_iff_limitingResidual_eq_zero.mpr hr
  apply sub_eq_zero.mpr
  apply paretoEquiv.injective
  change toPareto (closure.starProjection qOne) =
    toPareto (pFit paretoSquarefreeClosure qOne)
  rw [toPareto_pFit, toPareto_qOne]
  exact ha

theorem residual_eq_zero_iff_displacement_physically_bounded :
    limitingResidual = 0 ↔
      ∃ C : ℝ, ∀ k : ℕ, |qSequence displacement k| ≤ C := by
  constructor
  · intro hr
    refine ⟨0, ?_⟩
    intro k
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    cases k <;> simp [qSequence]
  · rintro ⟨C, hC⟩
    exact residual_eq_zero_of_displacement_physically_bounded C hC


/-- The displacement inherits the nonzero-mean annihilator's tail divergence. -/
theorem displacement_scaled_tail_tendsto (hr : limitingResidual ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * ‖tail N displacement‖ ^ 2) atTop atTop := by
  apply scaled_tail_transfer_sub (B pResidual) displacement
    (2 * (Real.sqrt zetaTwo * ‖pResidual‖) ^ 2 / zetaTwo)
  · intro N
    exact scaled_tail_energy_le_of_bounded (B pResidual) N
      (Real.sqrt zetaTwo * ‖pResidual‖) (by positivity)
      (B_physical_bound pResidual)
  · exact squarefree_annihilator_scaled_tail_tendsto witness witness_mem_orthogonal
      (fun hm => hr (residual_eq_zero_of_witness_mean_zero hm))

/-- Conditional research reduction: a frequently bounded scaled displacement tail. -/
theorem residual_zero_iff_frequently_bounded_displacement_tail :
    limitingResidual = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * ‖tail N displacement‖ ^ 2 ≤ C := by
  constructor
  · intro hr
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro N
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    simp [tail, finiteHead]
  · rintro ⟨C, hC⟩
    by_contra hr
    have hg := (displacement_scaled_tail_tendsto hr).eventually (eventually_gt_atTop C)
    obtain ⟨N, hN, hgt⟩ := (hC.and_eventually hg).exists
    exact (not_lt_of_ge hN) hgt

/-- The conclusion is Mathlib's RH; physical boundedness is the open premise. -/
theorem riemannHypothesis_of_displacement_bounded (C : ℝ)
    (hC : ∀ k : ℕ, |qSequence displacement k| ≤ C) : RiemannHypothesis := by
  have hr := residual_eq_zero_of_displacement_physically_bounded C hC
  have hm : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

/-- An even weaker regularity premise than global physical boundedness. -/
theorem riemannHypothesis_of_frequently_bounded_displacement_tail
    (h : ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * ‖tail N displacement‖ ^ 2 ≤ C) : RiemannHypothesis := by
  have hr := residual_zero_iff_frequently_bounded_displacement_tail.mpr h
  have hm : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
