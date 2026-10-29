/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.QExactHeadOptimizerComparison
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Coalescence of exact-head Q/P minimizers

Source: the user-provided CRT/Ramanujan/Pareto agenda, Priority 3, and the
head-aware affine optimizer comparison developed in this continuation.

The quantitative input is the sharp optimizer displacement bound with the
actual canonical Mobius exact-head vector as a feasible competitor. The
existing unconditional PNT-based sublinear complete energy then gives
`H * ‖D‖² → 0`, although the individual exact-head energies need not be
bounded. This is convergence of differences, not constant closure or RH.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QExactHeadOptimizerCoalescence
open ZetaTwoHilbert

/-- A sharp competitor bound and the existing unconditional complete-energy
provider force the stronger weighted squared displacement limit. -/
theorem scaled_displacement_tendsto_zero
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (D : ℕ → QHilbert)
    (hbound : ∀ j, 4 * ((H j : ℝ) + 1) * ((H j : ℝ) + 2) * ‖D j‖ ^ 2 ≤
      ‖QMobiusExactHead.exactHead (H j)‖ ^ 2) :
    Tendsto (fun j => (H j : ℝ) * ‖D j‖ ^ 2) atTop (𝓝 0) := by
  have hupper := QSquarefreeSublinearHeads.exactHead_sublinear.comp hH
  apply squeeze_zero (fun j => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) ?_ hupper
  intro j
  by_cases hzero : H j = 0
  · simp only [Function.comp_def, hzero, Nat.cast_zero, zero_mul, div_zero, le_refl]
  have hp : (0 : ℝ) < H j := by exact_mod_cast Nat.pos_of_ne_zero hzero
  apply (le_div_iff₀ hp).mpr
  have hc : (H j : ℝ) ^ 2 ≤
      4 * ((H j : ℝ) + 1) * ((H j : ℝ) + 2) := by
    nlinarith [sq_nonneg (H j : ℝ), Nat.cast_nonneg (α := ℝ) (H j)]
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖D j‖)
  nlinarith [hbound j]

/-- The unweighted squared displacement also vanishes. -/
theorem displacement_sq_tendsto_zero
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (D : ℕ → QHilbert)
    (hbound : ∀ j, 4 * ((H j : ℝ) + 1) * ((H j : ℝ) + 2) * ‖D j‖ ^ 2 ≤
      ‖QMobiusExactHead.exactHead (H j)‖ ^ 2) :
    Tendsto (fun j => ‖D j‖ ^ 2) atTop (𝓝 0) := by
  have hscaled := scaled_displacement_tendsto_zero H hH D hbound
  apply squeeze_zero' (Eventually.of_forall (fun j => sq_nonneg ‖D j‖)) ?_ hscaled
  filter_upwards [hH.eventually (eventually_ge_atTop (1 : ℕ))] with j hj
  have hreal : (1 : ℝ) ≤ H j := by exact_mod_cast hj
  nlinarith [sq_nonneg ‖D j‖]

/-- Norm coalescence of the optimizer differences. -/
theorem displacement_norm_tendsto_zero
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (D : ℕ → QHilbert)
    (hbound : ∀ j, 4 * ((H j : ℝ) + 1) * ((H j : ℝ) + 2) * ‖D j‖ ^ 2 ≤
      ‖QMobiusExactHead.exactHead (H j)‖ ^ 2) :
    Tendsto (fun j => ‖D j‖) atTop (𝓝 0) := by
  have hs := displacement_sq_tendsto_zero H hH D hbound
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

/-- Actual minimizers coalesce whenever the unconditional canonical exact-head
competitor lies in their common affine feasible set. -/
theorem affine_minimizers_scaled_coalescence
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (U : ℕ → Submodule ℝ QHilbert) (FQ FP : ℕ → QHilbert)
    (hU : ∀ j u, u ∈ U j → ∀ n < H j, u n = 0)
    (hcoset : ∀ j, FP j - FQ j ∈ U j)
    (hC : ∀ j, QMobiusExactHead.exactHead (H j) - FQ j ∈ U j)
    (hQ : ∀ j u, u ∈ U j → ‖FQ j‖ ^ 2 ≤ ‖FQ j + u‖ ^ 2)
    (hP : ∀ j u, u ∈ U j →
      ‖ZetaTwoParetoTransfer.toPareto (FP j)‖ ^ 2 ≤
        ‖ZetaTwoParetoTransfer.toPareto (FP j + u)‖ ^ 2) :
    Tendsto (fun j => (H j : ℝ) * ‖FP j - FQ j‖ ^ 2) atTop (𝓝 0) := by
  apply scaled_displacement_tendsto_zero H hH (fun j => FP j - FQ j)
  intro j
  exact QExactHeadOptimizerComparison.affine_minimizers_bound_of_competitor
    (H j) (U j) (FQ j) (FP j) (QMobiusExactHead.exactHead (H j))
    (hU j) (hcoset j) (hC j) (hQ j) (hP j)

/-- Norm form of actual affine optimizer coalescence. -/
theorem affine_minimizers_norm_coalescence
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (U : ℕ → Submodule ℝ QHilbert) (FQ FP : ℕ → QHilbert)
    (hU : ∀ j u, u ∈ U j → ∀ n < H j, u n = 0)
    (hcoset : ∀ j, FP j - FQ j ∈ U j)
    (hC : ∀ j, QMobiusExactHead.exactHead (H j) - FQ j ∈ U j)
    (hQ : ∀ j u, u ∈ U j → ‖FQ j‖ ^ 2 ≤ ‖FQ j + u‖ ^ 2)
    (hP : ∀ j u, u ∈ U j →
      ‖ZetaTwoParetoTransfer.toPareto (FP j)‖ ^ 2 ≤
        ‖ZetaTwoParetoTransfer.toPareto (FP j + u)‖ ^ 2) :
    Tendsto (fun j => ‖FP j - FQ j‖) atTop (𝓝 0) := by
  apply displacement_norm_tendsto_zero H hH (fun j => FP j - FQ j)
  intro j
  exact QExactHeadOptimizerComparison.affine_minimizers_bound_of_competitor
    (H j) (U j) (FQ j) (FP j) (QMobiusExactHead.exactHead (H j))
    (hU j) (hcoset j) (hC j) (hQ j) (hP j)

end RiemannResearch.RH.QExactHeadOptimizerCoalescence
