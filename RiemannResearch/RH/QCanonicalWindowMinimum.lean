/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoAffineMinimum
import RiemannResearch.RH.QCanonicalMetricAsymptotics
import RiemannResearch.RH.QCanonicalMovingCovariance
import RiemannResearch.RH.QMetricCorrectionBounds
import RiemannResearch.RH.QParetoGramComparison
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.CanonicalMobiusMovingCovariance
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.CanonicalResidualGramMinimum
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.Analysis.FiniteGramAffineMinimum
import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Actual canonical-window Q minima and unconditional Q/P optimizer stability

Source: continuation of the user's QCanonicalCofinalGramResearch20261015
handoff. The actual Q residual Gram inverse is constructed from the existing
proved independence of the complete P residual family. Both optimizers are
finite inverse-Gram constructions; no stationarity provider is assumed.

The unconditional conclusions concern the difference of the two minima and
the displacement of their minimizing vectors. Uniform boundedness of the
full optimized energy remains Open and is the conditional RH input below.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.QCanonicalWindowMinimum
open Pareto Pareto.CoefficientStabilization
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QParetoMetric QParetoGramComparison QParetoAffineMinimum
open RiemannResearch.Analysis.FiniteHilbertGram

def windowFamily (N M : ℕ) (i : Fin (M - N + 1)) : QHilbert :=
  QCanonicalMovingCovariance.residual (N + i.val)

theorem paretoFamily_window (N M : ℕ) :
    paretoFamily (windowFamily N M) = canonicalWindowResidual N M := by
  funext i
  exact QCanonicalMovingCovariance.toPareto_residual (N + i.val)

theorem windowFamily_head_zero (N M : ℕ) :
    ∀ i k, 0 < k → k ≤ N → qSequence (windowFamily N M i) k = 0 := by
  intro i k hk hkN
  exact QCanonicalMetricAsymptotics.residual_head_zero (N + i.val) k hk (by omega)

theorem windowFamily_linearIndependent (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    LinearIndependent ℝ (windowFamily N M) := by
  apply (linearIndependent_iff_injective_fintypeLinearCombination).mpr
  intro c d hcd
  apply (canonicalWindowResidual_linearIndependent N M hN hNM).fintypeLinearCombination_injective
  have h := congrArg toPareto hcd
  simpa only [toPareto_synthesis, paretoFamily_window] using h

/-- The genuine Q inverse-Gram normal vector, not an assumed solution. -/
def normalQ (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) : Fin (M - N + 1) → ℝ :=
  (gramEquiv (windowFamily_linearIndependent N M hN hNM)).symm (fun _ => 1)

theorem normalQ_normal (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    gram (windowFamily N M) (normalQ N M hN hNM) = fun _ => 1 :=
  (gramEquiv (windowFamily_linearIndependent N M hN hNM)).apply_symm_apply _

theorem normalQ_mass_pos (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    0 < ∑ i, normalQ N M hN hNM i :=
  normal_mass_pos _ _ (normalQ_normal N M hN hNM)

theorem normalP_normal (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    gram (paretoFamily (windowFamily N M))
      (canonicalWindowNormal N M hN hNM) = fun _ => 1 := by
  rw [paretoFamily_window]
  exact canonicalWindowNormal_normal N M hN hNM

def optimalResidual (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) : QHilbert :=
  affineVector (windowFamily N M) (normalQ N M hN hNM)

/-- The P optimizer, reencoded with Q weights to preserve its physical sequence. -/
def paretoOptimalResidual (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) : QHilbert :=
  affineVector (windowFamily N M) (canonicalWindowNormal N M hN hNM)

theorem optimalResidual_energy (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    ‖optimalResidual N M hN hNM‖ ^ 2 = (∑ i, normalQ N M hN hNM i)⁻¹ :=
  affineCoefficients_energy _ _ (normalQ_normal N M hN hNM)

/-- Complete Q energy for every affine competitor, including its signed remainder. -/
theorem optimalResidual_completion (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (a : Fin (M - N + 1) → ℝ) (ha : ∑ i, a i = 1) :
    ‖Fintype.linearCombination ℝ (windowFamily N M) a‖ ^ 2 =
      ‖optimalResidual N M hN hNM‖ ^ 2 +
        ‖Fintype.linearCombination ℝ (windowFamily N M)
          (a - affineCoefficients (normalQ N M hN hNM))‖ ^ 2 := by
  rw [optimalResidual_energy]
  exact affineCoefficients_completion _ _ _ (normalQ_normal N M hN hNM) ha

theorem optimalResidual_minimum_iff (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (a : Fin (M - N + 1) → ℝ) (ha : ∑ i, a i = 1) :
    ‖Fintype.linearCombination ℝ (windowFamily N M) a‖ ^ 2 =
      ‖optimalResidual N M hN hNM‖ ^ 2 ↔
        a = affineCoefficients (normalQ N M hN hNM) := by
  rw [optimalResidual_energy]
  constructor
  · intro he
    exact (windowFamily_linearIndependent N M hN hNM).fintypeLinearCombination_injective
      ((affineCoefficients_minimum_iff _ _ _ (normalQ_normal N M hN hNM) ha).mp he)
  · rintro rfl
    exact affineCoefficients_energy _ _ (normalQ_normal N M hN hNM)

theorem paretoOptimalResidual_energy (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    ‖toPareto (paretoOptimalResidual N M hN hNM)‖ ^ 2 =
      (canonicalWindowMass N M hN hNM)⁻¹ := by
  rw [paretoOptimalResidual, toPareto_affineVector, paretoFamily_window]
  exact affineCoefficients_energy _ _ (canonicalWindowNormal_normal N M hN hNM)

theorem paretoOptimalResidual_energy_le (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    ‖toPareto (paretoOptimalResidual N M hN hNM)‖ ^ 2 ≤
      ‖Pareto.MovingCovariance.residual N‖ ^ 2 := by
  have h := pareto_minimum_le_vertex (windowFamily N M)
    (canonicalWindowNormal N M hN hNM) (normalP_normal N M hN hNM)
    (⟨0, by omega⟩ : Fin (M - N + 1))
  simpa only [paretoOptimalResidual, windowFamily, Nat.add_zero,
    QCanonicalMovingCovariance.toPareto_residual] using h

/-- No l1 or l2 bound on either actual optimizing coefficient vector is needed. -/
theorem paretoOptimalResidual_correction_le (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    metricCorrection (paretoOptimalResidual N M hN hNM) ≤
      Pareto.MovingCovariance.energyRate N := by
  have hc := metricCorrection_le_of_head_zero (paretoOptimalResidual N M hN hNM) N
    (synthesis_head_zero (windowFamily N M)
      (affineCoefficients (canonicalWindowNormal N M hN hNM)) N
      (windowFamily_head_zero N M))
  exact hc.trans (div_le_div_of_nonneg_right
    (paretoOptimalResidual_energy_le N M hN hNM) (by positivity))

/-- Exact correction balance for the two actual inverse-Gram optimizers. -/
theorem optimizer_correction_balance (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    metricCorrection (paretoOptimalResidual N M hN hNM) =
      metricCorrection (optimalResidual N M hN hNM) +
        2 * ‖toPareto (optimalResidual N M hN hNM -
          paretoOptimalResidual N M hN hNM)‖ ^ 2 +
        metricCorrection (optimalResidual N M hN hNM -
          paretoOptimalResidual N M hN hNM) :=
  correction_balance _ _ _ (normalP_normal N M hN hNM) (normalQ_normal N M hN hNM)

/-- The actual Q optimum has a vanishing correction without a coefficient budget. -/
theorem optimalResidual_correction_le (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    metricCorrection (optimalResidual N M hN hNM) ≤
      Pareto.MovingCovariance.energyRate N := by
  have hb := optimizer_correction_balance N M hN hNM
  have hp := paretoOptimalResidual_correction_le N M hN hNM
  nlinarith only [hb, hp,
    sq_nonneg ‖toPareto (optimalResidual N M hN hNM -
      paretoOptimalResidual N M hN hNM)‖,
    metricCorrection_nonneg (optimalResidual N M hN hNM -
      paretoOptimalResidual N M hN hNM)]

/-- The complete mixed Q/P Gram correction is controlled for two windows
whose heads and upper cutoffs may vary independently. -/
theorem optimized_gram_correction_sq_le
    (N M K L : ℕ) (hN : 0 < N) (hNM : N ≤ M) (hK : 0 < K) (hKL : K ≤ L) :
    (QParetoMetric.metricPairing (optimalResidual N M hN hNM)
      (optimalResidual K L hK hKL)) ^ 2 ≤
      Pareto.MovingCovariance.energyRate N * Pareto.MovingCovariance.energyRate K := by
  exact (QMetricCorrectionBounds.metricPairing_sq_le _ _).trans
    (mul_le_mul (optimalResidual_correction_le N M hN hNM)
      (optimalResidual_correction_le K L hK hKL)
      (metricCorrection_nonneg _) (Pareto.MovingCovariance.energyRate_nonneg _))

theorem optimized_energy_gap_bounds (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    0 ≤ zetaTwo * ‖optimalResidual N M hN hNM‖ ^ 2 -
        ‖toPareto (paretoOptimalResidual N M hN hNM)‖ ^ 2 ∧
      zetaTwo * ‖optimalResidual N M hN hNM‖ ^ 2 -
        ‖toPareto (paretoOptimalResidual N M hN hNM)‖ ^ 2 ≤
          Pareto.MovingCovariance.energyRate N := by
  have h := minimum_energy_gap (windowFamily N M)
    (canonicalWindowNormal N M hN hNM) (normalQ N M hN hNM)
    (normalP_normal N M hN hNM) (normalQ_normal N M hN hNM)
  exact ⟨h.1, h.2.trans (paretoOptimalResidual_correction_le N M hN hNM)⟩

theorem optimizer_displacement_sq_le (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    ‖toPareto (optimalResidual N M hN hNM -
        paretoOptimalResidual N M hN hNM)‖ ^ 2 ≤
      Pareto.MovingCovariance.energyRate N / ((N : ℝ) + 1) := by
  exact (displacement_sq_le_correction (windowFamily N M)
    (canonicalWindowNormal N M hN hNM) (normalQ N M hN hNM)
    (normalP_normal N M hN hNM) (normalQ_normal N M hN hNM) N
    (windowFamily_head_zero N M)).trans
      (div_le_div_of_nonneg_right (paretoOptimalResidual_correction_le N M hN hNM)
        (by positivity))

/-- Absolute discrepancy of the actual minima tends to zero, uniformly in
how fast the upper cutoff and the finite dimension grow. -/
theorem cofinal_optimized_energy_gap_tendsto_zero
    (N M : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNM : ∀ j, N j ≤ M j)
    (hcofinal : Tendsto N atTop atTop) :
    Tendsto (fun j => zetaTwo * ‖optimalResidual (N j) (M j) (hN j) (hNM j)‖ ^ 2 -
      ‖toPareto (paretoOptimalResidual (N j) (M j) (hN j) (hNM j))‖ ^ 2)
      atTop (𝓝 0) :=
  squeeze_zero
    (fun j => (optimized_energy_gap_bounds (N j) (M j) (hN j) (hNM j)).1)
    (fun j => (optimized_energy_gap_bounds (N j) (M j) (hN j) (hNM j)).2)
    (QCanonicalMetricAsymptotics.pareto_energyRate_tendsto_zero.comp hcofinal)

/-- Unconditional strong convergence of the difference of the minimizers.
This does not assert strong convergence of either minimizer separately. -/
theorem cofinal_optimizer_displacement_tendsto_zero
    (N M : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNM : ∀ j, N j ≤ M j)
    (hcofinal : Tendsto N atTop atTop) :
    Tendsto (fun j => optimalResidual (N j) (M j) (hN j) (hNM j) -
      paretoOptimalResidual (N j) (M j) (hN j) (hNM j)) atTop (𝓝 0) := by
  let e : ℕ → QHilbert := fun j =>
    optimalResidual (N j) (M j) (hN j) (hNM j) -
      paretoOptimalResidual (N j) (M j) (hN j) (hNM j)
  have hs : Tendsto (fun j => ‖toPareto (e j)‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _
      (QCanonicalMetricAsymptotics.pareto_energyRate_tendsto_zero.comp hcofinal)
    intro j
    exact (optimizer_displacement_sq_le (N j) (M j) (hN j) (hNM j)).trans
      (div_le_self (Pareto.MovingCovariance.energyRate_nonneg _)
        (by have := Nat.cast_nonneg (α := ℝ) (N j); linarith))
  have ht : Tendsto (fun j => toPareto (e j)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  apply (tendsto_toPareto_iff e 0).mp
  simpa only [show toPareto (0 : QHilbert) = 0 from toParetoLinear.map_zero] using ht

/-- Conditional research reduction. Open: a uniform bound on these actual
Q inverse-Gram minimum energies. All finite normal equations, legality and
growing-head interpolation are supplied internally. -/
theorem riemannHypothesis_of_bounded_optimized_energy
    (M : ℕ → ℕ) (hM : ∀ j, j + 1 ≤ M j) (C : ℝ)
    (hbudget : ∀ j, ‖optimalResidual (j + 1) (M j) (by omega) (hM j)‖ ^ 2 ≤ C) :
    RiemannHypothesis := by
  let F : ℕ → ThresholdHilbert := fun j =>
    canonicalWindowTrial (j + 1) (M j)
      (canonicalWindowOptimum (j + 1) (M j) (by omega) (hM j))
  refine riemannHypothesis_of_bounded_exact_head_errors F ?_ ?_ (zetaTwo * C) ?_
  · intro j
    unfold F canonicalWindowTrial
    rw [Fintype.linearCombination_apply]
    exact closedSpace.sum_mem (fun i _ => closedSpace.smul_mem _
      (canonicalMobiusHilbert_mem_closedSpace _))
  · intro j k hk hkj
    exact canonicalWindowTrial_exact_head _ _ _
      (canonicalWindowOptimum_sum _ _ _ _) k hk (by omega)
  · intro j
    have h := (optimized_energy_gap_bounds (j + 1) (M j) (by omega) (hM j)).1
    have he : ‖hilbertOne - F j‖ ^ 2 =
        ‖toPareto (paretoOptimalResidual (j + 1) (M j) (by omega) (hM j))‖ ^ 2 := by
      dsimp [F]
      rw [canonicalWindow_optimal_energy, paretoOptimalResidual_energy]
    rw [he]
    exact (sub_nonneg.mp h).trans
      (mul_le_mul_of_nonneg_left (hbudget j) zetaTwo_pos.le)

/-- Conditional research reduction in inverse-Gram form. Open: a common
positive lower bound on the actual normal masses along growing heads. -/
theorem riemannHypothesis_of_normalQ_mass_lower
    (M : ℕ → ℕ) (hM : ∀ j, j + 1 ≤ M j) (c : ℝ) (hc : 0 < c)
    (hcapacity : ∀ j, c ≤ ∑ i, normalQ (j + 1) (M j) (by omega) (hM j) i) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_bounded_optimized_energy M hM (1 / c)
  intro j
  rw [optimalResidual_energy]
  simpa only [one_div] using one_div_le_one_div_of_le hc (hcapacity j)

end RiemannResearch.RH.QCanonicalWindowMinimum
