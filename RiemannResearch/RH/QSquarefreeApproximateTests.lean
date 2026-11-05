/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.ApproximateSquareTests
import RiemannResearch.RH.QSquarefreePrimeLocalTests
import RiemannResearch.RH.QSquarefreeResponsePhysicalTail
/-!
# Normalized local tests for the actual displacement
Source: the user's approximate weighted local-test argument.
The normalized-test limit is an open arithmetic premise.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeApproximateTests
open ZetaTwoHilbert QSquarefreeDisplacementRigidity
open RiemannResearch.NumberTheory.ApproximateSquareTests
theorem riemannHypothesis_of_normalized_weighted_tests
    (ht : Tendsto (fun n : ℕ =>
      weightedTest (qSequence displacement) n / (n : ℝ) ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply QSquarefreePrimeLocalTests.riemannHypothesis_of_difference_tendsto_zero
  exact difference_tendsto_zero_of_normalized_test _
    (qSequence_div_nat_tendsto_zero displacement)
    (fun n hn => QSquarefreeMultiplierRigidity.closure_difference_square
      displacement_mem n hn) ht
end RiemannResearch.RH.QSquarefreeApproximateTests
