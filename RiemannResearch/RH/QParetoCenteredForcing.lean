/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoPrimorialForcing
import RiemannResearch.RH.QParetoDisplacementResolvent
import RiemannResearch.Analysis.ProjectionTrialEnergy
import RiemannResearch.RH.QPrimorialResidualCertificate

/-!
# Centered signed certificates for the actual Pareto forcing

Source: Pareto-first research agenda, Priority 3, 11 November 2026.
The normal equations permit centering before taking a norm. The exact
remainder gives a reciprocal-moment variance bound, stronger than the
universal one-quarter energy estimate whenever the moments certify it.
Cofinal decay of the actual upper endpoints remains an Open obligation.
-/
noncomputable section
namespace RiemannResearch.RH.QParetoCenteredForcing
open Pareto ZetaTwoHilbert QParetoDisplacementResolvent
open RiemannResearch.Analysis

variable (T : Submodule ℝ ThresholdHilbert) [T.HasOrthogonalProjection]

theorem centered_projection (r : ThresholdHilbert) (hr : T.starProjection r = 0)
    (alpha : ℝ) :
    T.starProjection (reciprocalD r - alpha • r) = T.starProjection (reciprocalD r) := by
  simp only [map_sub, map_smul, hr, smul_zero, sub_zero]

/-- Exact signed identity; the omitted residual is a nonnegative square. -/
theorem centered_energy_identity (r : ThresholdHilbert) (hr : T.starProjection r = 0)
    (alpha : ℝ) :
    ‖T.starProjection (reciprocalD r)‖ ^ 2 +
      ‖reciprocalD r - alpha • r - T.starProjection (reciprocalD r)‖ ^ 2 =
      ‖reciprocalD r‖ ^ 2 - 2 * alpha * inner ℝ r (reciprocalD r) +
        alpha ^ 2 * ‖r‖ ^ 2 := by
  have h := projection_trial_energy T (reciprocalD r - alpha • r) 0 (T.zero_mem)
  rw [sub_zero, sub_zero, centered_projection T r hr alpha, norm_sub_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right,
    real_inner_comm r (reciprocalD r)] at h
  linarith

theorem centered_energy_bound (r : ThresholdHilbert) (hr : T.starProjection r = 0)
    (alpha : ℝ) :
    ‖T.starProjection (reciprocalD r)‖ ^ 2 ≤
      ‖reciprocalD r‖ ^ 2 - 2 * alpha * inner ℝ r (reciprocalD r) +
        alpha ^ 2 * ‖r‖ ^ 2 := by
  linarith [centered_energy_identity T r hr alpha,
    sq_nonneg ‖reciprocalD r - alpha • r - T.starProjection (reciprocalD r)‖]

/-- Optimal scalar centering is the variance of the reciprocal multiplier. -/
theorem variance_bound (r : ThresholdHilbert) (hr : T.starProjection r = 0)
    :
    ‖T.starProjection (reciprocalD r)‖ ^ 2 ≤
      ‖reciprocalD r‖ ^ 2 -
        (inner ℝ r (reciprocalD r)) ^ 2 / ‖r‖ ^ 2 := by
  have h := centered_energy_bound T r hr (inner ℝ r (reciprocalD r) / ‖r‖ ^ 2)
  by_cases he : ‖r‖ ^ 2 = 0
  · simpa only [he, div_zero, zero_mul, mul_zero, sub_zero, add_zero, zero_pow] using h
  · convert h using 1
    field_simp [he]
    ring

/-- Uniform off-diagonal estimate for the positive reciprocal contraction. -/
theorem forcing_energy_le_quarter (r : ThresholdHilbert)
    (hr : T.starProjection r = 0) :
    ‖T.starProjection (reciprocalD r)‖ ^ 2 ≤ (1 / 4 : ℝ) * ‖r‖ ^ 2 := by
  have h := centered_energy_bound T r hr (1 / 2)
  have hd := reciprocal_norm_sq_le_energy r
  nlinarith

/-- A rational centering and three complete moment endpoints give a scalar certificate. -/
theorem moment_endpoint (r : ThresholdHilbert) (hr : T.starProjection r = 0)
    (alpha ehi mlo nhi : ℝ) (halpha : 0 ≤ alpha)
    (he : ‖r‖ ^ 2 ≤ ehi) (hm : mlo ≤ inner ℝ r (reciprocalD r))
    (hn : ‖reciprocalD r‖ ^ 2 ≤ nhi) :
    ‖T.starProjection (reciprocalD r)‖ ^ 2 ≤ nhi - 2 * alpha * mlo + alpha ^ 2 * ehi := by
  have h := centered_energy_bound T r hr alpha
  have h₁ := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * alpha by positivity)
  have h₂ := mul_le_mul_of_nonneg_left he (sq_nonneg alpha)
  linarith

open QParetoPrimorialForcing QPrimorialMatchedDisplacement

theorem actual_residual_projected_zero (n : ℕ) :
    (paretoStage n).starProjection (residual n) = 0 := by
  unfold QParetoPrimorialForcing.residual
  rw [map_sub, Submodule.starProjection_eq_self_iff.mpr
    ((paretoStage n).starProjection_apply_mem hilbertOne), sub_self]

theorem actual_forcing_energy_le_quarter (n : ℕ) :
    ‖forcing n‖ ^ 2 ≤ (1 / 4 : ℝ) * pError n := by
  have h := forcing_energy_le_quarter (paretoStage n) (residual n)
    (actual_residual_projected_zero n)
  simpa only [forcing, residual_eq_physical, pError] using h

theorem actual_moment_endpoint (n : ℕ) (alpha ehi mlo nhi : ℝ) (halpha : 0 ≤ alpha)
    (he : pError n ≤ ehi)
    (hm : mlo ≤ inner ℝ (residual n) (reciprocalD (residual n)))
    (hn : ‖reciprocalD (residual n)‖ ^ 2 ≤ nhi) :
    ‖forcing n‖ ^ 2 ≤ nhi - 2 * alpha * mlo + alpha ^ 2 * ehi := by
  apply moment_endpoint (paretoStage n) (residual n)
    (actual_residual_projected_zero n) alpha ehi mlo nhi halpha _ hm hn
  simpa only [residual_eq_physical, pError] using he

open ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric QParetoDisplacementBounds
open QParetoClosedProjectionComparison QSquarefreePrimorialCofinality
open QSquarefreeMeasureRigidity QSquarefreeDisplacementRigidity QPrimorialPrimeCarry
open QPrimorialResidualCertificate
open RiemannResearch.Analysis.NestedOrthogonalDecomposition
open Filter
open scoped Topology BigOperators


open QPrimorialMatchedGram RiemannResearch.Analysis.FiniteHilbertGram

theorem actual_normal_row_zero (n : ℕ) (i : DivisorIndex n) :
    inner ℝ (paretoDivisorAtom n i) (residual n) = 0 := by
  have hm : paretoDivisorAtom n i ∈ paretoStage n := by
    rw [← synthesisSpan_eq n]
    exact Submodule.subset_span ⟨i, rfl⟩
  exact Submodule.inner_right_of_mem_orthogonal hm
    (Submodule.sub_starProjection_mem_orthogonal (K := paretoStage n) hilbertOne)

theorem paretoSequence_reciprocalD (f : ThresholdHilbert) (k : ℕ) :
    hilbertSequence (reciprocalD f) k = hilbertSequence f k / (k : ℝ) := by
  cases k with
  | zero => simp only [hilbertSequence_zero, Nat.cast_zero, zero_div]
  | succ n =>
    rw [hilbertSequence_succ, hilbertSequence_succ, reciprocalD_apply]
    push_cast
    ring

/-- Exact physical signed row: centering occurs before any absolute estimate. -/
theorem actual_rhs_centered_physical (n : ℕ) (i : DivisorIndex n) (alpha : ℝ) :
    rhs n i = ∑' k : ℕ, positiveWeight k *
      (ArithmeticCumulative.residueFraction (divisorConductor n i) k *
        ((1 / (k : ℝ) - alpha) * qSequence (qOne - pOptimizer n) k)) := by
  have he : rhs n i = inner ℝ (paretoDivisorAtom n i)
      (reciprocalD (residual n) - alpha • residual n) := by
    rw [inner_sub_right, real_inner_smul_right, actual_normal_row_zero, mul_zero, sub_zero]
    rfl
  rw [he, hilbert_inner_weighted]
  unfold paretoInner
  apply tsum_congr
  intro k
  simp only [hilbertSequence_sub, hilbertSequence_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, paretoSequence_reciprocalD, paretoDivisorAtom, toPareto_sequence,
    qSequence_qResidue, residual_eq_physical]
  ring

/-- The actual canonical finite forcing converges; its limit is not presumed zero. -/
theorem actual_forcing_tendsto :
    Tendsto forcing atTop
      (𝓝 (paretoSquarefreeClosure.starProjection (reciprocalD (toPareto pResidual)))) := by
  have hq : Tendsto (fun n => qOne - pOptimizer n) atTop (𝓝 pResidual) :=
    tendsto_const_nhds.sub pOptimizer_tendsto
  have hr : Tendsto residual atTop (𝓝 (toPareto pResidual)) := by
    simpa only [Function.comp_def, toParetoCLM_apply, ← residual_eq_physical] using
      toParetoCLM.continuous.continuousAt.tendsto.comp hq
  apply projection_moving_input_tendsto paretoStage
    (reciprocalD.continuous.continuousAt.tendsto.comp hr)
  simpa only [paretoStage_closure] using
    Submodule.starProjection_tendsto_closure_iSup paretoStage
      (fun _ _ h => Submodule.map_mono (primorialStage_mono h))
      (reciprocalD (toPareto pResidual))

theorem actual_displacement_norm_le_forcing (n : ℕ) :
    ‖toPareto (stageDisplacement n)‖ ≤ ‖forcing n‖ := by
  have hd := normal_equation_strong (primorialStage n) (paretoStage n)
    (toPareto_mem_stage_iff n) qOne
  have hr : toPareto (qOne - pFit (paretoStage n) qOne) = residual n :=
    (residual_eq_physical n).symm
  rw [hr] at hd
  apply displacement_le_forcing (paretoStage n) (toPareto (stageDisplacement n)) (forcing n)
    ((toPareto_mem_stage_iff n _).mpr (stageDisplacement_mem n))
  exact hd

/-- A finite complete forcing certificate controls the entire finite residual energy. -/
theorem actual_pError_cube_le_forcing (n : ℕ) :
    (pError n)^3 ≤ max ((8 / ((n : ℝ) + 3))^3) (128 * ‖forcing n‖ ^ 2) := by
  have hd := actual_displacement_norm_le_forcing n
  have hd2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hd
  have hm := norm_identity (stageDisplacement n)
  have hc := reciprocal_energy_le (toPareto (stageDisplacement n))
  change inner ℝ (toPareto (stageDisplacement n))
    (reciprocalD (toPareto (stageDisplacement n))) ≤ _ at hc
  change zetaTwo * ‖stageDisplacement n‖ ^ 2 =
    ‖toPareto (stageDisplacement n)‖ ^ 2 +
      inner ℝ (toPareto (stageDisplacement n))
        (reciprocalD (toPareto (stageDisplacement n))) at hm
  have hp := (primeStage n).norm_starProjection_apply_le (stageDisplacement n)
  have hp2 : ‖primeComponent n‖ ^ 2 ≤ ‖stageDisplacement n‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp
  have hpz := mul_le_mul_of_nonneg_left hp2 zetaTwo_pos.le
  have hbound : 64 * zetaTwo * ‖primeComponent n‖ ^ 2 ≤ 128 * ‖forcing n‖ ^ 2 := by
    nlinarith only [hd2, hm, hc, hpz]
  exact (pError_cube_le_primeComponent n).trans (max_le_max_left _ hbound)

/-- A single computed stage bounds the limiting residual, with no convergence-rate premise. -/
theorem limiting_pError_cube_le_forcing_endpoint (n : ℕ) (U : ℝ)
    (hU : ‖forcing n‖ ^ 2 ≤ U) :
    (‖toPareto pResidual‖ ^ 2)^3 ≤ max ((8 / ((n : ℝ) + 3))^3) (128 * U) := by
  have hpow : (‖toPareto pResidual‖ ^ 2)^3 ≤ (pError n)^3 := by
    gcongr
    exact limiting_pError_le n
  exact hpow.trans ((actual_pError_cube_le_forcing n).trans
    (max_le_max_left _ (mul_le_mul_of_nonneg_left hU (by norm_num))))

/-- Conditional consumer only: the cofinal small-endpoint provider is not supplied here. -/
theorem residual_zero_of_cofinal_forcing_endpoints (N : ℕ → ℕ) (U : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (hU : Tendsto U atTop (𝓝 0))
    (hbound : ∀ j, ‖forcing (N j)‖ ^ 2 ≤ U j) :
    pResidual = 0 := by
  have htop : Tendsto (fun j => (N j : ℝ) + 3) atTop atTop :=
    tendsto_atTop_mono (fun j => by
      change (N j : ℝ) ≤ (N j : ℝ) + 3
      linarith) (tendsto_natCast_atTop_atTop.comp hN)
  have ht : Tendsto
      (fun j => max ((8 / ((N j : ℝ) + 3))^3) (128 * U j)) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, max_self] using
      ((htop.const_div_atTop 8).pow 3).max (hU.const_mul 128)
  have hle : (‖toPareto pResidual‖ ^ 2)^3 ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds ht (fun j =>
      limiting_pError_cube_le_forcing_endpoint (N j) (U j) (hbound j))
  have hz : (‖toPareto pResidual‖ ^ 2)^3 = 0 :=
    le_antisymm hle (pow_nonneg (sq_nonneg _) _)
  have hz2 : ‖toPareto pResidual‖ ^ 2 = 0 := (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hz
  have hzv : toPareto pResidual = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz2)
  apply QParetoEquivalence.paretoEquiv.injective
  simpa only [map_zero, QParetoEquivalence.paretoEquiv_apply] using hzv


end RiemannResearch.RH.QParetoCenteredForcing
