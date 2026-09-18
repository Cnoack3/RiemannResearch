/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FreshCoprimeSchur
import RiemannResearch.Analysis.CorrelationNormalizedCorrection

/-!
# Final finite-dimensional consequences of the coupled-residual chat

Source: user-provided CRT/coupled Pareto residual discussion, September 2026.
This module closes two finite-dimensional bookkeeping gaps:

* the signed fresh Schur remainder has the expected trace lower bound;
* the exact optimum can be written explicitly as the sum of the transported
  projection increment and the fresh Schur fit.

Neither theorem assumes or proves the open logarithmic lower bound for the
actual gain.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoupledResidual

open RiemannResearch.Analysis.CorrelationCorrection
open RiemannResearch.LinearAlgebra
open FiniteTwoSeedCompletion RamanujanLaguerre AdjacentPacket

/-- Squared actual correlations of the transported-screened fresh columns. -/
def freshSourceSquare (M : ℕ) : ℝ :=
  ∑ i, (inner ℝ (screenedFresh M i) (transportError M)) ^ 2

/-- Trace of the actual signed Gram matrix of the screened fresh columns. -/
def freshTrace (M : ℕ) : ℝ :=
  ∑ i, ‖screenedFresh M i‖ ^ 2

/-- The crude trace lower bound for the exact fresh Schur remainder. All
mixed terms remain inside the inverse-Gram optimum; only the last comparison
uses the trace. -/
theorem fresh_trace_lower (M : ℕ) (hT : 0 < freshTrace M) :
    freshSourceSquare M / freshTrace M ≤ freshRemainder M := by
  have h := normal_equations_trace_bound (transportError M) (screenedFresh M)
    (freshCoefficients M) (freshFit_normal M)
  have hfit :
      finiteSchurCombination (screenedFresh M) (freshCoefficients M) = freshFit M := rfl
  rw [hfit, freshFit_norm_sq] at h
  have hs : freshSourceSquare M ≤ freshTrace M * freshRemainder M := by
    simpa [freshSourceSquare, freshTrace] using h
  apply (div_le_iff₀ hT).2
  simpa [mul_comm] using hs

/-- Screening against the transported space cannot increase the fresh Gram
trace. This is the precise first step in the manuscript's raw-norm fallback. -/
theorem freshTrace_le_rawTrace (M : ℕ) :
    freshTrace M ≤ ∑ i, ‖freshFamily M i‖ ^ 2 := by
  unfold freshTrace
  apply Finset.sum_le_sum
  intro i hi
  exact screened_norm_sq_le (transportedSpace M) (freshFamily M i)

/-- The normalized exact optimum is literally the transported projection
increment plus the fresh signed Schur fit. Thus no cross term has been
discarded in the transported/fresh assembly. -/
theorem decomposed_reconstruction_optimum (M : ℕ) (hg : 0 < gain M) :
    let w := (distance M / gain M) •
      (((transportedSpace M).starProjection hilbertOne - fit M) + freshFit M)
    w ∈ budgetHilbert (2 * M) ∧
      w ∈ (budgetHilbert M)ᗮ ∧
      inner ℝ (error M) w = distance M ∧
      ‖w‖ ^ 2 = distance M ^ 2 / gain M := by
  dsimp only
  have heq :
      ((transportedSpace M).starProjection hilbertOne - fit M) + freshFit M =
        fit (2 * M) - fit M := by
    rw [doubled_fit_eq_transport_add_fresh]
    abel
  rw [heq]
  exact optimal_normalized_increment (budgetHilbert M) (budgetHilbert (2 * M))
    (budgetHilbert_mono (by omega : M ≤ 2 * M)) hilbertOne (distance M) hg

end RiemannResearch.RH.Pareto.CoupledResidual
