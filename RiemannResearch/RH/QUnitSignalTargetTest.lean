/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.UnitSignalProjection
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace

/-!
# A single-test RH consumer for sampled unit-signal approximants

Source: continuation of the user-provided boundedness audit, 22 October 2026.
The exact signed single-test identity implies strong convergence without a
prior projection limit or a uniform norm bound. Membership in the actual legal
span then gives RH by the existing complete-Q-to-Pareto Mellin theorem.

Conditional research reduction: true admissibility, legality, a fixed test in
all trial spaces with nonzero target pairing, vanishing test discrepancy and sampling
displacement are explicit hypotheses. No arithmetic provider of the scalar
discrepancy limit is asserted.
-/

noncomputable section
open Filter
open scoped Topology


namespace RiemannResearch.RH.QUnitSignalTargetTest
open ZetaTwoHilbert
open RiemannResearch.Analysis.UnitSignalProjection

/-- Conditional RH reduction with a single scalar testing obligation and
a separate vanishing sampling error. No boundedness or projection-limit
assumption is needed. -/
theorem riemannHypothesis_of_sampled_single_test
    (Ms : ℕ → ProjectionSignalModel QHilbert) (F : ℕ → QHilbert) (v : QHilbert)
    (htarget : ∀ n, (Ms n).target = qOne)
    (hmass : ∀ n, (Ms n).mass = 1)
    (hF : ∀ n, (Ms n).Admissible (F n))
    (hlegal : ∀ n, F n ∈ QFullResidueProjection.legalSpan)
    (hv : ∀ n, v ∈ (Ms n).space)
    (hsignal : inner ℝ qOne v ≠ 0)
    (htest : Tendsto (fun n => inner ℝ (F n - qOne) v) atTop (𝓝 0))
    (happrox : Tendsto (fun n => F n - (Ms n).optimizer) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hconv := ProjectionSignalModel.admissible_tendsto_of_single_test
    Ms F qOne v 1 htarget hmass hF hv hsignal htest happrox
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  exact mem_closure_of_tendsto hconv (Filter.Eventually.of_forall hlegal)

end RiemannResearch.RH.QUnitSignalTargetTest
