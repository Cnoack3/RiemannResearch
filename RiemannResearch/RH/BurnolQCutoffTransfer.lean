/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.BurnolParetoTransfer
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Linarith

/-!
# Burnol cutoff bounds in the actual Q geometry

Source: J.-F. Burnol, arXiv:math/0103058v2 (2001), Theorem 1.3,
for the external analytic lower bound. This module proves its transfer,
retaining the exact nonnegative Q/P metric correction and the same maximal
conductor. Every theorem exposes `ContinuousCutoffLowerBound` as an input;
the source's analytic theorem is not established here. Arbitrary finite
conductor subsets include squarefree cutoffs and primorial divisor sets.
-/
open scoped BigOperators ENNReal
noncomputable section
namespace RiemannResearch.RH.BurnolQCutoffTransfer
open ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer QParetoMetric
open Pareto.BurnolTransfer

/-- Complete metric correction retained in the cutoff transfer. -/
theorem finite_error_lower_with_correction (N : ℕ) (hN : 1 ≤ N) (L : ℝ)
    (h : ContinuousCutoffLowerBound N L) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d ∧ d ≤ N) :
    L + metricCorrection (qOne - ∑ d ∈ s, a d • qResidue d) ≤
      zetaTwo * ‖qOne - ∑ d ∈ s, a d • qResidue d‖ ^ 2 := by
  have hp := finite_error_lower_of_continuous N hN L h s a hs
  have hm : toPareto (qOne - ∑ d ∈ s, a d • qResidue d) =
      Pareto.hilbertOne - Pareto.BaezDuarte.finiteResidueSum s a := by
    calc
      toPareto (qOne - ∑ d ∈ s, a d • qResidue d) =
          toPareto qOne - toPareto (∑ d ∈ s, a d • qResidue d) :=
        toParetoLinear.map_sub _ _
      _ = _ := by rw [toPareto_qOne,
        toPareto_finiteResidueSum s a (fun d hd => (hs d hd).1)]
  rw [norm_identity, hm]
  linarith

/-- Scalar Q lower bound, conditional on the continuous envelope. -/
theorem finite_error_lower (N : ℕ) (hN : 1 ≤ N) (L : ℝ)
    (h : ContinuousCutoffLowerBound N L) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d ∧ d ≤ N) :
    L / zetaTwo ≤ ‖qOne - ∑ d ∈ s, a d • qResidue d‖ ^ 2 := by
  have hh := finite_error_lower_with_correction N hN L h s a hs
  have hc := metricCorrection_nonneg (qOne - ∑ d ∈ s, a d • qResidue d)
  apply (div_le_iff₀ zetaTwo_pos).mpr
  nlinarith

/-- The logarithm uses the maximal conductor, including for primorial stages. -/
theorem finite_error_log_envelope (N : ℕ) (hN : 1 ≤ N) (c : ℝ)
    (h : ContinuousCutoffLowerBound N (c / Real.log N))
    (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d ∧ d ≤ N) :
    c / (zetaTwo * Real.log N) ≤
      ‖qOne - ∑ d ∈ s, a d • qResidue d‖ ^ 2 := by
  simpa only [div_div, mul_comm] using
    finite_error_lower N hN (c / Real.log N) h s a hs

end RiemannResearch.RH.BurnolQCutoffTransfer
