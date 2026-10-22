/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalStageGain
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.FiniteWeightedTailCharge
import RiemannResearch.RH.QRationalWeightComparison
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rational displacement and complete-Q projection gains

Source: user-provided signed-tail continuation agenda, 20 October 2026,
Priority 3. These comparisons retain complete infinite Q tails. The exact
mismatch identity keeps the signed cross term; rational optimizer movement
is not identified with the true Q projection gain.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoHilbert ZetaTwoProbability QSquarefreePrimorialCofinality
open Pareto.SquarefreeStageExhaustion

/-- Two-sided complete-Q comparison for any vector in an actual primorial stage. -/
theorem primorial_rational_norm_comparison {m : ℕ} {v : QHilbert}
    (hv : v ∈ primorialStage m) :
    zetaTwo * ‖v‖^2 ≤
        ∑ a ∈ sites (primorialPeriod m), weight (primorialPeriod m) a * (qSequence v a)^2 ∧
      (∑ a ∈ sites (primorialPeriod m), weight (primorialPeriod m) a * (qSequence v a)^2) ≤
        (5 / 3 : ℝ) * zetaTwo * ‖v‖^2 := by
  obtain ⟨C, hC⟩ := qSequence_bounded_of_mem hv
  have hb (a : ℕ) : |1 - qSequence v a| ≤ 1 + C := by
    calc
      |1 - qSequence v a| ≤ 1 + |qSequence v a| := by
        simpa [sub_eq_add_neg] using abs_add_le (1 : ℝ) (-qSequence v a)
      _ ≤ 1 + C := add_le_add (le_refl 1) (hC a)
  have hp (a : ℕ) : 1 - qSequence v (a + primorialPeriod m) = 1 - qSequence v a := by
    rw [qSequence_periodic_of_mem hv]
  have h := periodic_rationalError_comparison (primorialPeriod m)
    (primorialPeriod_pos m) (fun a => 1 - qSequence v a) hb hp
  have he (a : ℕ) : 1 - (1 - qSequence v a) = qSequence v a := by ring
  unfold rationalError RiemannResearch.Analysis.FiniteWeightedTailCharge.energy at h
  simp_rw [he] at h
  rw [← qNorm_eq_inversePowerMean] at h
  exact h

/-- The actual optimizer displacement is comparable to its complete-Q norm,
uniformly in the moving coefficients. -/
theorem rationalStageDisplacement_qNorm_comparison {n m : ℕ} (hnm : n ≤ m) :
    zetaTwo * ‖rationalMinimizer (primorialPeriod n) -
        rationalMinimizer (primorialPeriod m)‖^2 ≤ rationalStageDisplacement n m ∧
      rationalStageDisplacement n m ≤ (5 / 3 : ℝ) * zetaTwo *
        ‖rationalMinimizer (primorialPeriod n) - rationalMinimizer (primorialPeriod m)‖^2 := by
  have hv := (primorialStage m).sub_mem
    (primorialStage_mono hnm (rationalMinimizer_mem n)) (rationalMinimizer_mem m)
  have hs : qSequence (rationalMinimizer (primorialPeriod n) -
      rationalMinimizer (primorialPeriod m)) =
      fun a => qSequence (rationalMinimizer (primorialPeriod n)) a -
        qSequence (rationalMinimizer (primorialPeriod m)) a := by
    exact qSequenceLinear.map_sub _ _
  simpa only [hs, rationalStageDisplacement] using primorial_rational_norm_comparison hv

/-- Exact comparison with true Q projection gain, retaining both mismatch
energy and its signed cross term. -/
theorem rational_displacement_projection_gain_exact {n m : ℕ} (hnm : n ≤ m) :
    ‖rationalMinimizer (primorialPeriod m) - rationalMinimizer (primorialPeriod n)‖^2 =
      primorialError n - primorialError m +
      ‖(rationalMinimizer (primorialPeriod m) - primorialOptimizer m) -
        (rationalMinimizer (primorialPeriod n) - primorialOptimizer n)‖^2 +
      2 * inner ℝ (primorialOptimizer m - primorialOptimizer n)
        ((rationalMinimizer (primorialPeriod m) - primorialOptimizer m) -
          (rationalMinimizer (primorialPeriod n) - primorialOptimizer n)) := by
  have hgain : primorialError n = primorialError m +
      ‖primorialOptimizer m - primorialOptimizer n‖^2 := by
    exact RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy
      (primorialStage n) (primorialStage m) (primorialStage_mono hnm) qOne
  have he : rationalMinimizer (primorialPeriod m) - rationalMinimizer (primorialPeriod n) =
      (primorialOptimizer m - primorialOptimizer n) +
      ((rationalMinimizer (primorialPeriod m) - primorialOptimizer m) -
        (rationalMinimizer (primorialPeriod n) - primorialOptimizer n)) := by abel
  rw [he, norm_add_sq_real]
  linarith

end RiemannResearch.RH.QRationalCoprimeTail
