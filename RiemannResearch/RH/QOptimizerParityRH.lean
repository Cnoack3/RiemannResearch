/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QOptimizerParity
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ParetoLegalApproximationClosure

/-!
# The actual Q parity and Parseval sufficient conditions for RH

Source: the user's Q approximation program, 13 October 2026. The full legal
residue closure is transferred to the actual Pareto closure by the existing
continuous sequence-preserving map. Mellin separation then gives RH. The
zero-limit hypotheses remain explicit; RH is never an input to these results.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QFullResidueProjection
open ZetaTwoHilbert QDivisorHilbert ZetaTwoParetoTransfer
open Pareto
open Pareto.CoefficientStabilization

/-- The continuous transfer preserves the entire full legal closure. -/
theorem paretoOne_mem_closedSpace_of_qOne_mem_full_closure
    (h : qOne ∈ closure) : hilbertOne ∈ closedSpace := by
  let K : Submodule ℝ QHilbert := closedSpace.comap toParetoCLM.toLinearMap
  have hspan : legalSpan ≤ K := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change toPareto (qResidue (i + 2)) ∈ closedSpace
    rw [toPareto_residueAtom]
    exact (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
      (Submodule.subset_span ⟨i, rfl⟩)
  have hpclosed : IsClosed (closedSpace : Set ThresholdHilbert) := by
    change IsClosed (_root_.closure
      (Submodule.span ℝ (Set.range residueAtom) : Set ThresholdHilbert))
    exact isClosed_closure
  have hKclosed : IsClosed (K : Set QHilbert) :=
    hpclosed.preimage toParetoCLM.continuous
  have hqclosure : qOne ∈ _root_.closure (legalSpan : Set QHilbert) := h
  have hm : qOne ∈ K := (closure_minimal hspan hKclosed) hqclosure
  change toParetoCLM qOne ∈ closedSpace at hm
  simpa only [toParetoCLM_apply, toPareto_qOne] using hm

/-- A full-Q legal approximation is sufficient for RH, through the existing
Pareto Mellin separation theorem. No converse assumption is used. -/
theorem riemannHypothesis_of_qOne_mem_full_closure
    (h : qOne ∈ closure) : RiemannHypothesis := by
  apply Pareto.riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn)
  exact closedSpace_le_legalClosure
    (paretoOne_mem_closedSpace_of_qOne_mem_full_closure h)

/-- The complete optimizer energy tending to zero is sufficient for RH. -/
theorem riemannHypothesis_of_residual_energy_tendsto_zero
    (h : Tendsto (fun n => ‖qOne - candidate n‖ ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (residual_energy_tendsto_zero_iff.mp h)

/-- Only the parity-coordinate limit is needed, once the coefficients are
those of the actual full-Q orthogonal projections. -/
theorem riemannHypothesis_of_residual_parity_tendsto_zero
    (h : Tendsto (fun n => inner ℝ (qOne - candidate n) (divisorWavelet 2))
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (residual_parity_tendsto_zero_iff.mp h)

/-- Literal arithmetic Parseval energy, with every Jordan-weighted mode
retained, supplies the same sufficient condition for RH. -/
theorem riemannHypothesis_of_arithmetic_parseval_tendsto_zero
    (h : Tendsto
      (fun n => ∑' r : ℕ+,
        ((if r = 1 then (1 : ℝ) else 0) -
          ∑ i : Fin n, coefficients n i *
            qResidueDivisorCoefficient (conductor n i) (r : ℕ)) ^ 2 /
          qJordanTwo (r : ℕ)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_residual_energy_tendsto_zero
  simpa only [qSynthesis_error_parseval, candidate] using h

end RiemannResearch.RH.QFullResidueProjection
