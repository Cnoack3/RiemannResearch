/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ProjectionResponseEndpoint
import RiemannResearch.Analysis.ProjectionInnovationSeries
import RiemannResearch.RH.QSquarefreeResponseSeries
import RiemannResearch.RH.QCanonicalInnovation
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Factor-one squarefree response endpoint bound

Source: user-provided endpoint argument and item 3 of
`InfiniteSquarefreeResponseResearch20261027.md`, commit
abd42dee58b969ce9c28ecfbf3cfec1e974c8b1a, for the statement and proof strategy.

Both canonical-stage and physical-coordinate tails are complete infinite
sums. Zero and dependent innovations remain at their original indices.
No residual-vanishing or arithmetic regularity hypothesis is assumed.
-/

noncomputable section
namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionVariation
open RiemannResearch.Analysis.ProjectionInnovationSeries
open RiemannResearch.Analysis.ProjectionResponseEndpoint
open RiemannResearch.Analysis.SingleDirectionProjection
open scoped BigOperators

theorem stage_le_closure (N : ℕ) : stage N ≤ ZetaTwoOptimizerStage.closure :=
  (walkSpan_le squarefreeAtom id N).trans
    (Submodule.span ℝ (Set.range squarefreeAtom)).le_topologicalClosure

/-- Parseval's individual term, including the zero innovation case. -/
theorem projection_increment_norm_sq (f : QHilbert) (N : ℕ) :
    ‖increment squarefreeAtom id f N‖ ^ 2 =
      (inner ℝ f (direction N)) ^ 2 := by
  have he : increment squarefreeAtom id f N =
      (inner ℝ f (direction N)) • direction N := by
    change (stage (N + 1)).starProjection f - (stage N).starProjection f = _
    rw [projection_succ]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  by_cases hN : direction N = 0
  · simp [hN]
  · rw [direction_norm N hN]
    simp

/-- Exact complete coefficient-tail identity; no active-index re-enumeration. -/
theorem projection_tail_energy (f : QHilbert) (N : ℕ) :
    ‖ZetaTwoOptimizerStage.closure.starProjection f - (stage N).starProjection f‖ ^ 2 =
      ∑' j, (inner ℝ f (direction (j + N))) ^ 2 := by
  calc
    _ = ∑' j, ‖increment squarefreeAtom id f (j + N)‖ ^ 2 :=
      (increment_tail_energy squarefreeAtom id f N).symm
    _ = _ := tsum_congr (fun j => projection_increment_norm_sq f (j + N))

/-- The tail projection after B has its complete Hilbert--Schmidt bound. -/
theorem projection_B_tail_norm_sq_le (N : ℕ) (f : QHilbert) :
    ‖ZetaTwoOptimizerStage.closure.starProjection (B f) -
      (stage N).starProjection (B f)‖ ^ 2 ≤ ‖f‖ ^ 2 * smoothingTail N := by
  have hs : Summable (fun j => (inner ℝ (B f) (direction (j + N))) ^ 2) := by
    simpa only [projection_increment_norm_sq] using
      increment_energy_summable squarefreeAtom id (B f) N
  have hc (j : ℕ) : (inner ℝ (B f) (direction (j + N))) ^ 2 ≤
      ‖f‖ ^ 2 * ‖B (direction (j + N))‖ ^ 2 := by
    rw [B_symmetric]
    have h := mul_self_le_mul_self (abs_nonneg (inner ℝ f (B (direction (j + N)))))
      (abs_real_inner_le_norm f (B (direction (j + N))))
    simpa only [← pow_two, sq_abs, mul_pow] using h
  rw [projection_tail_energy]
  calc
    _ ≤ ∑' j, ‖f‖ ^ 2 * ‖B (direction (j + N))‖ ^ 2 :=
      Summable.tsum_le_tsum hc hs ((B_direction_tail_summable N).mul_left (‖f‖ ^ 2))
    _ = ‖f‖ ^ 2 * smoothingTail N := by rw [tsum_mul_left]; rfl

/-- Exact signed endpoint displacement, retaining both outputs. -/
theorem movingCorrection_endpoint_eq (N : ℕ) :
    correction - movingCorrection N =
      (ZetaTwoOptimizerStage.closure.starProjection (B limitingResidual) -
        (stage N).starProjection (B limitingResidual)) -
      (stage N).starProjection (B (ZetaTwoOptimizerStage.closure.starProjection qOne -
        (stage N).starProjection qOne)) := by
  exact response_difference_eq (stage N) ZetaTwoOptimizerStage.closure B qOne

theorem movingCorrection_endpoint_orthogonal (N : ℕ) :
    inner ℝ
      (ZetaTwoOptimizerStage.closure.starProjection (B limitingResidual) -
        (stage N).starProjection (B limitingResidual))
      ((stage N).starProjection (B (ZetaTwoOptimizerStage.closure.starProjection qOne -
        (stage N).starProjection qOne))) = 0 :=
  projection_difference_inner_projection_eq_zero _ _ (stage_le_closure N) _ _

/-- Exact orthogonal endpoint energy, distinct from squared increment sums. -/
theorem movingCorrection_endpoint_norm_sq (N : ℕ) :
    ‖correction - movingCorrection N‖ ^ 2 =
      ‖ZetaTwoOptimizerStage.closure.starProjection (B limitingResidual) -
        (stage N).starProjection (B limitingResidual)‖ ^ 2 +
      ‖(stage N).starProjection (B (ZetaTwoOptimizerStage.closure.starProjection qOne -
        (stage N).starProjection qOne))‖ ^ 2 := by
  exact response_difference_norm_sq (stage N) ZetaTwoOptimizerStage.closure
    (stage_le_closure N) B qOne

/-- The actual endpoint has factor-one control by the remaining residual
energy and the full infinite smoothing tail, at every canonical stage. -/
theorem movingCorrection_endpoint_norm_sq_le (N : ℕ) :
    ‖correction - movingCorrection N‖ ^ 2 ≤ error N * smoothingTail N := by
  exact response_difference_norm_sq_le (stage N) ZetaTwoOptimizerStage.closure
    (stage_le_closure N) B B_symmetric (smoothingTail N)
    (tsum_nonneg (fun _ => sq_nonneg _)) (projection_B_tail_norm_sq_le N) qOne

/-- Complete target-coefficient energy tail. -/
def targetEnergyTail (N : ℕ) : ℝ := ∑' j, (targetCoefficient (j + N)) ^ 2

/-- Exact identification of A_N with the residual energy excess. -/
theorem targetEnergyTail_eq_error_sub (N : ℕ) :
    targetEnergyTail N = error N - ‖limitingResidual‖ ^ 2 := by
  have hp := projection_tail_energy qOne N
  have he := walkError_eq_limitingError_add squarefreeAtom id qOne N
  change ‖ZetaTwoOptimizerStage.closure.starProjection qOne -
    (stage N).starProjection qOne‖ ^ 2 = targetEnergyTail N at hp
  change error N = ‖limitingResidual‖ ^ 2 +
    ‖ZetaTwoOptimizerStage.closure.starProjection qOne -
      (stage N).starProjection qOne‖ ^ 2 at he
  linarith

end RiemannResearch.RH.QCanonicalInnovation
