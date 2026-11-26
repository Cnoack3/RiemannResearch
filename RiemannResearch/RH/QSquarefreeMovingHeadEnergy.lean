/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QPolylogMovingHeadEnergy
import RiemannResearch.RH.QSquarefreeLogResidualTail
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.ParetoSquarefreeDampingConverse
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A cofinal weighted-energy criterion on moving physical heads

Source: the user's squarefree moving-head program.
This replaces pointwise control at every stage by a frequent bound on one
finite weighted energy. The physical head may grow arbitrarily slowly.
The bounded-energy premise remains an Open arithmetic obligation.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeMovingHeadEnergy
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QAnnihilatorTailEscape QPolylogTailEnergy
open QSquarefreeLogResidualTail QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.LogTailWeights

/-- A weighted-energy bound is sufficient even if it holds only cofinally
and the physical head grows more slowly than the projection stage. -/
theorem residual_zero_of_frequently_moving_head_energy_bound
    (k : ℕ) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hbound : ∃ᶠ N : ℕ in atTop,
      weightedHeadEnergy k (H N) (movingCorrection N) ≤ C) :
    limitingResidual = 0 := by
  obtain ⟨hs, htotal⟩ :=
    weightedEnergy_summable_of_frequently_moving_head_bound k
      movingCorrection correction movingCorrection_tendsto H hH C hbound
  have htail (N : ℕ) : logWeight k N * ‖tail N correction‖ ^ 2 ≤
      ((k : ℝ)+6)^k * C := by
    have hprofile := (profile_mul_tail_energy_le k N correction hs).trans htotal
    have h1 := mul_le_mul_of_nonneg_right
      (logWeight_le_polylogTailProfile k N) (sq_nonneg ‖tail N correction‖)
    have h2 := mul_le_mul_of_nonneg_left hprofile
      (pow_nonneg (by positivity : 0 ≤ (k : ℝ)+6) k)
    nlinarith
  exact (residual_zero_iff_correction_frequently_bounded_log_scaled_tail k).mpr
    ⟨((k : ℝ)+6)^k * C, (Eventually.of_forall htail).frequently⟩

/-- A nonzero actual residual forces every expanding weighted head energy
to diverge, however slowly the physical cutoff grows. -/
theorem moving_head_energy_tendsto_atTop_of_residual_ne_zero
    (k : ℕ) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hr : limitingResidual ≠ 0) :
    Tendsto (fun N => weightedHeadEnergy k (H N) (movingCorrection N))
      atTop atTop := by
  apply tendsto_atTop.2
  intro C
  have hnot : ¬ ∃ᶠ N : ℕ in atTop,
      weightedHeadEnergy k (H N) (movingCorrection N) ≤ C := by
    intro hb
    exact hr (residual_zero_of_frequently_moving_head_energy_bound k H hH C hb)
  simp only [Filter.Frequently, not_not, not_le] at hnot
  exact hnot.mono (fun N hN => hN.le)

/-- Conditional research reduction. A finite weighted head budget replaces
the all-stage pointwise polylogarithmic envelope. -/
theorem riemannHypothesis_of_frequently_moving_head_energy_bound
    (k : ℕ) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hbound : ∃ᶠ N : ℕ in atTop,
      weightedHeadEnergy k (H N) (movingCorrection N) ≤ C) :
    RiemannHypothesis := by
  have hr := residual_zero_of_frequently_moving_head_energy_bound k H hH C hbound
  have hm : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

/-- Unconditional sub-profile growth of actual squarefree head energies.
The bounded-head-energy premise sufficient for RH remains open. -/
theorem moving_head_energy_div_profile_tendsto_zero
    (k : ℕ) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun N => weightedHeadEnergy k (H N) (movingCorrection N) /
      polylogTailProfile k (H N)) atTop (𝓝 0) :=
  weightedHeadEnergy_div_profile_tendsto_zero k movingCorrection correction
    movingCorrection_tendsto H hH

/-- The unconditional asymptotic estimate in standard little-o notation. -/
theorem moving_head_energy_isLittleO_profile
    (k : ℕ) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    (fun N => weightedHeadEnergy k (H N) (movingCorrection N)) =o[atTop]
      (fun N => polylogTailProfile k (H N)) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).2
    (moving_head_energy_div_profile_tendsto_zero k H hH)
  filter_upwards [((polylogTailProfile_tendsto_atTop k).comp hH).eventually
    (eventually_gt_atTop (0 : ℝ))] with N hN
  exact fun hz => False.elim ((ne_of_gt hN) hz)

/-- The normalized energy vanishes uniformly over every squarefree stage.
The unnormalized constant-energy bound sufficient for RH is not asserted. -/
theorem moving_head_energy_uniform_subprofile
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ H : ℕ in atTop, ∀ N : ℕ,
      weightedHeadEnergy k H (movingCorrection N) ≤ ε * polylogTailProfile k H :=
  weightedHeadEnergy_uniform_subprofile k movingCorrection correction
    movingCorrection_tendsto ε hε

/-- A common bound only needs one stage N ≥ H for each test head H. -/
theorem residual_zero_of_joint_head_budget (k : ℕ) (C : ℝ)
    (hb : ∀ H : ℕ, ∃ N ≥ H, weightedHeadEnergy k H (movingCorrection N) ≤ C) :
    limitingResidual = 0 := by
  choose F hF hbF using hb
  have htop : Tendsto F atTop atTop := tendsto_atTop.2 fun h =>
    (eventually_ge_atTop h).mono fun n hn => hn.trans (hF n)
  obtain ⟨hs, ht⟩ := weightedEnergy_summable_of_frequently_moving_head_bound k
    (fun n => movingCorrection (F n)) correction (movingCorrection_tendsto.comp htop)
    id tendsto_id C (Eventually.of_forall hbF).frequently
  apply (residual_zero_iff_correction_frequently_bounded_log_scaled_tail k).mpr
  refine ⟨((k : ℝ) + 6)^k * C, (Eventually.of_forall ?_).frequently⟩
  intro H
  have h₁ := mul_le_mul_of_nonneg_right
    (logWeight_le_polylogTailProfile k H) (sq_nonneg ‖tail H correction‖)
  have h₂ := mul_le_mul_of_nonneg_left
    ((profile_mul_tail_energy_le k H correction hs).trans ht)
    (pow_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 6) k)
  nlinarith only [h₁, h₂]

/-- Independent positive bounded budgets may shrink arbitrarily fast with the
head. The same witnessing stage works simultaneously for every weight index. -/
theorem riemannHypothesis_iff_simultaneous_head_budgets (b : ℕ → ℝ)
    (hb : ∀ H, 0 < b H) (hbound : ∃ C : ℝ, ∀ H, b H ≤ C) :
    RiemannHypothesis ↔ ∀ H : ℕ, ∃ N ≥ H, ∀ k : ℕ,
      weightedHeadEnergy k H (movingCorrection N) ≤ b H := by
  constructor
  · intro hRH
    have hm : qOne ∈ ZetaTwoOptimizerStage.closure := by
      rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
      exact qSquarefreeClosure_iff_paretoSquarefreeClosure.mpr
        (Pareto.ResidueMellin.hilbertOne_mem_squarefreeClosure_of_riemannHypothesis hRH)
    have hr : limitingResidual = 0 :=
      sub_eq_zero.mpr (Submodule.starProjection_eq_self_iff.mpr hm).symm
    have hu : Tendsto movingCorrection atTop (𝓝 0) := by
      simpa only [correction, hr, map_zero] using movingCorrection_tendsto
    intro H
    have hp : Tendsto (fun N => (H : ℝ) * ‖movingCorrection N‖ ^ 2) atTop (𝓝 0) := by
      simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
        (hu.norm.pow 2).const_mul (H : ℝ)
    obtain ⟨N, hN, hsmall⟩ := ((eventually_ge_atTop H).and
      (hp.eventually (Iio_mem_nhds (hb H)))).exists
    refine ⟨N, hN, fun k => ?_⟩
    exact (weightedHeadEnergy_le_profile_norm_sq k H (movingCorrection N)).trans
      ((mul_le_mul_of_nonneg_right ((polylogTailProfile_le_logWeight k H).trans
        (logWeight_le_nat k H)) (sq_nonneg _)).trans hsmall.le)
  · intro h
    obtain ⟨C, hC⟩ := hbound
    have hr := residual_zero_of_joint_head_budget 0 C (fun H => by
      obtain ⟨N, hN, hE⟩ := h H
      exact ⟨N, hN, (hE 0).trans (hC H)⟩)
    have hm : qOne ∈ ZetaTwoOptimizerStage.closure :=
      Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
    exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
      (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

end RiemannResearch.RH.QSquarefreeMovingHeadEnergy
