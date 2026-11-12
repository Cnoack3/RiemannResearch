/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoPrimorialForcing
import RiemannResearch.RH.QSimultaneousCRT
import RiemannResearch.RH.QUnconditionalAtomSeries
import RiemannResearch.RH.QParetoCumulativeGains

/-!
# Admissible moving CRT blocks in the Pareto-first construction

Source: Pareto-first research agenda, Priority 7, 11 November 2026.
Coefficients and the complete finite dictionary depend on the stage.
The ordered block differences converge to the actual Pareto projection.
No separate convergence of the prime and carry blocks is presumed.
The fixed unordered-atom obstruction also holds in the Pareto metric.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QParetoAdmissibleLimits
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open QSquarefreePrimorialCofinality QPrimorialMatchedGram QPrimorialMatchedDisplacement
open QSquarefreeMeasureRigidity QParetoClosedProjectionComparison QSimultaneousCRT

def primeBlock (n : ℕ) : QHilbert :=
  ∑ i, paretoCoefficients n i • primeSynthesis (divisorConductor n i)

def carryBlock (n : ℕ) : QHilbert :=
  ∑ i, paretoCoefficients n i • canonicalCarry (divisorConductor n i)

/-- The exact finite signed identity uses the current stage's coefficient vector. -/
theorem block_difference_eq_optimizer (n : ℕ) :
    primeBlock n - carryBlock n = pOptimizer n := by
  rw [primeBlock, carryBlock, ← Finset.sum_sub_distrib, pOptimizer_expansion]
  unfold QCovarianceInverse.qSynthesis
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_sub, ← residue_eq_prime_sub_carry]

/-- Convergence is in the complete Q norm, using physical identification of the P optimizer. -/
theorem block_difference_tendsto :
    Tendsto (fun n => primeBlock n - carryBlock n) atTop
      (𝓝 (pFit paretoSquarefreeClosure qOne)) := by
  simpa only [block_difference_eq_optimizer] using pOptimizer_tendsto

/-- The same ordered blocks converge in the complete P norm to the P projection. -/
theorem pareto_block_difference_tendsto :
    Tendsto (fun n => toPareto (primeBlock n - carryBlock n)) atTop
      (𝓝 (paretoSquarefreeClosure.starProjection hilbertOne)) := by
  have h := toParetoCLM.continuous.continuousAt.tendsto.comp block_difference_tendsto
  simpa only [Function.comp_def, toParetoCLM_apply, toPareto_pFit, toPareto_qOne] using h


/-- Exact complete P tail between two ordered finite blocks. -/
theorem finite_block_tail_energy (n m : ℕ) (hnm : n ≤ m) :
    ‖toPareto (primeBlock m - carryBlock m) -
      toPareto (primeBlock n - carryBlock n)‖ ^ 2 = pError n - pError m := by
  rw [block_difference_eq_optimizer, block_difference_eq_optimizer]
  have h := RiemannResearch.Analysis.NestedProjectionGains.energy_drop
    (paretoStage n) (paretoStage m) (Submodule.map_mono (primorialStage_mono hnm)) hilbertOne
  rw [QParetoCumulativeGains.pError_eq, QParetoCumulativeGains.pError_eq]
  simpa only [pOptimizer, toPareto_pFit, toPareto_qOne] using h.symm

/-- Exact norm-tail energy to the actual limiting projection, without a zero-residual premise. -/
theorem complete_block_tail_energy (n : ℕ) :
    ‖paretoSquarefreeClosure.starProjection hilbertOne -
      toPareto (primeBlock n - carryBlock n)‖ ^ 2 =
      pError n - ‖toPareto QSquarefreeDisplacementRigidity.pResidual‖ ^ 2 := by
  apply tendsto_nhds_unique
    ((pareto_block_difference_tendsto.sub tendsto_const_nhds).norm.pow 2)
  apply (tendsto_const_nhds.sub pError_tendsto).congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (finite_block_tail_energy n m hm).symm

/-- Physical transfer preserves a complete Q tail bound for the same ordered blocks. -/
theorem complete_q_block_tail_bound (n : ℕ) :
    ZetaTwoProbability.zetaTwo *
      ‖pFit paretoSquarefreeClosure qOne - (primeBlock n - carryBlock n)‖ ^ 2 ≤
      2 * (pError n - ‖toPareto QSquarefreeDisplacementRigidity.pResidual‖ ^ 2) := by
  have h := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (pFit paretoSquarefreeClosure qOne - (primeBlock n - carryBlock n))
  rw [toPareto_sub, toPareto_pFit, toPareto_qOne, complete_block_tail_energy] at h
  exact h

/-- Convergence to the constant is exactly the still unresolved target-membership condition. -/
theorem pareto_block_target_iff :
    Tendsto (fun n => toPareto (primeBlock n - carryBlock n)) atTop (𝓝 hilbertOne) ↔
      hilbertOne ∈ paretoSquarefreeClosure := by
  constructor
  · intro h
    exact Submodule.starProjection_eq_self_iff.mp
      (tendsto_nhds_unique pareto_block_difference_tendsto h)
  · intro h
    simpa only [Submodule.starProjection_eq_self_iff.mpr h] using
      pareto_block_difference_tendsto

/-- Separate block limits, if supplied, must subtract to the actual projection. -/
theorem separated_stage_limits (P C : QHilbert)
    (hP : Tendsto primeBlock atTop (𝓝 P)) (hC : Tendsto carryBlock atTop (𝓝 C)) :
    P - C = pFit paretoSquarefreeClosure qOne :=
  tendsto_nhds_unique (hP.sub hC) block_difference_tendsto

/-- Given a prime-block limit, convergence of the difference supplies the carry-block limit. -/
theorem carry_limit_of_prime_limit (P : QHilbert)
    (hP : Tendsto primeBlock atTop (𝓝 P)) :
    Tendsto carryBlock atTop (𝓝 (P - pFit paretoSquarefreeClosure qOne)) := by
  have h := hP.sub block_difference_tendsto
  simpa only [sub_sub_cancel] using h

/-- The unconditional atom obstruction survives the physical change of measure. -/
theorem no_fixed_unordered_pareto_target (c : ℕ → ℝ) :
    ¬ HasSum (fun j => c j • toPareto (qResidue (j + 2))) hilbertOne := by
  intro h
  have ht := toQCLM.hasSum h
  apply QUnconditionalAtomSeries.no_hasSum_qOne c
  have h1 : toQ hilbertOne = qOne := by rw [← toPareto_qOne, toQ_toPareto]
  change HasSum (fun j => toQLinear (c j • toPareto (qResidue (j + 2))))
    (toQ hilbertOne) at ht
  simp only [map_smul] at ht
  change HasSum (fun j => c j • toQ (toPareto (qResidue (j + 2))))
    (toQ hilbertOne) at ht
  simpa only [toQ_toPareto, h1] using ht

/-- Any finite block retains the exact signed prime-minus-carry cancellation after transfer. -/
theorem finite_pareto_crt_identity (s : Finset ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ s, c d • toPareto (qResidue d)) =
      (∑ d ∈ s, c d • toPareto (primeSynthesis d)) -
        ∑ d ∈ s, c d • toPareto (canonicalCarry d) := by
  have h := congrArg toParetoLinear (finite_synthesis_identity s c)
  change (∑ d ∈ s, c d • toParetoLinear (qResidue d)) =
    (∑ d ∈ s, c d • toParetoLinear (primeSynthesis d)) -
      ∑ d ∈ s, c d • toParetoLinear (canonicalCarry d)
  simpa only [map_sub, map_sum, map_smul] using h

end RiemannResearch.RH.QParetoAdmissibleLimits
