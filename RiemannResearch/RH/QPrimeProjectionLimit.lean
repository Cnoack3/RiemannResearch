/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeProjectionControl
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quantitative prime control of the actual infinite displacement

Source: the 5 November 2026 audit of *Projection Displacement, Prime Atoms,
and Carries*, page 3. Strong convergence of both actual finite projections
passes the finite cubic estimate to their infinite limits. Prime-component
vanishing remains the explicit hypothesis in the zero-displacement theorem.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity

open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QParetoClosedProjectionComparison
open ZetaTwoOptimizerStage QSquarefreeFiniteDisplacement QSquarefreeMeasureRigidity

/-- The cubic finite bounds pass to a fixed closed subspace containing all
prime atoms. Both limiting vectors are the actual projections of one. -/
theorem pResidual_cube_le_prime_projection
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W) :
    (‖toPareto pResidual‖ ^ 2) ^ 3 ≤
      64 * zetaTwo * ‖W.starProjection displacement‖ ^ 2 := by
  have hp : Tendsto (fun N => toPareto (qOne - finitePFit N)) atTop
      (𝓝 (toPareto pResidual)) :=
    (paretoEquiv.continuous.tendsto pResidual).comp
      (tendsto_const_nhds.sub finitePFit_tendsto)
  have hleft : Tendsto
      (fun N => (‖toPareto (qOne - finitePFit N)‖ ^ 2) ^ 3) atTop
      (𝓝 ((‖toPareto pResidual‖ ^ 2) ^ 3)) :=
    (hp.norm.pow 2).pow 3
  have hd : Tendsto (fun N => W.starProjection (finiteDisplacement N)) atTop
      (𝓝 (W.starProjection displacement)) :=
    (W.starProjection.continuous.tendsto displacement).comp finiteDisplacement_tendsto
  have hright : Tendsto
      (fun N => 64 * zetaTwo * ‖W.starProjection (finiteDisplacement N)‖ ^ 2) atTop
      (𝓝 (64 * zetaTwo * ‖W.starProjection displacement‖ ^ 2)) :=
    (hd.norm.pow 2).const_mul (64 * zetaTwo)
  have hsmall_base : Tendsto
      (fun N : ℕ => (8 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto
      (fun N : ℕ => ((8 : ℝ) / ((N : ℝ) + 1)) ^ 3) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 3 ≠ 0)] using hsmall_base.pow 3
  have hsum : Tendsto
      (fun N : ℕ => ((8 : ℝ) / ((N : ℝ) + 1)) ^ 3 +
        64 * zetaTwo * ‖W.starProjection (finiteDisplacement N)‖ ^ 2) atTop
      (𝓝 (64 * zetaTwo * ‖W.starProjection displacement‖ ^ 2)) := by
    simpa only [zero_add] using hsmall.add hright
  apply le_of_tendsto_of_tendsto hleft hsum
  apply Filter.Eventually.of_forall
  intro N
  have hfinite := finitePResidual_cube_le_prime_projection N W (fun p hp _ => hW p hp)
  apply hfinite.trans
  apply max_le_iff.mpr
  constructor
  · exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) zetaTwo_pos.le) (sq_nonneg _))
  · exact le_add_of_nonneg_left (by positivity)

/-- Vanishing of the actual prime-visible displacement forces the actual
Pareto residual to vanish. -/
theorem pResidual_eq_zero_of_prime_projection_eq_zero
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)
    (hz : W.starProjection displacement = 0) :
    pResidual = 0 := by
  have h := pResidual_cube_le_prime_projection W hW
  simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  have hn : ‖toPareto pResidual‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hnot
    have hpos : 0 < ‖toPareto pResidual‖ := lt_of_not_ge hnot
    have hpow : 0 < (‖toPareto pResidual‖ ^ 2) ^ 3 := by positivity
    exact (not_lt_of_ge h) hpow
  apply paretoEquiv.injective
  change toPareto pResidual = toPareto (0 : QHilbert)
  rw [show toPareto (0 : QHilbert) = 0 from toParetoLinear.map_zero]
  exact norm_eq_zero.mp hn

/-- The actual displacement vanishes when its projection onto a subspace
containing every prime atom vanishes. -/
theorem displacement_eq_zero_of_prime_projection_eq_zero
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)
    (hz : W.starProjection displacement = 0) :
    displacement = 0 := by
  have hpzero := pResidual_eq_zero_of_prime_projection_eq_zero W hW hz
  have htrial := q_trial_identity closure paretoSquarefreeClosure
    toPareto_mem_paretoSquarefreeClosure_iff qOne
  change ‖pResidual‖ ^ 2 = ‖limitingResidual‖ ^ 2 + ‖displacement‖ ^ 2 at htrial
  rw [hpzero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at htrial
  apply norm_eq_zero.mp
  nlinarith [sq_nonneg ‖limitingResidual‖, norm_nonneg displacement]

theorem prime_projection_eq_zero_iff_displacement_eq_zero
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W) :
    W.starProjection displacement = 0 ↔ displacement = 0 := by
  constructor
  · exact displacement_eq_zero_of_prime_projection_eq_zero W hW
  · intro hd
    simp only [hd, map_zero]

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
