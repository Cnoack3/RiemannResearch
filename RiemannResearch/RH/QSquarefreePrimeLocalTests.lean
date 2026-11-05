/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.PrimeMultiplierRigidity
import RiemannResearch.NumberTheory.SquareDifferenceRigidity
import RiemannResearch.RH.QSquarefreeMultiplierRigidity
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSquarefreeResponsePhysicalTail
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Lean.Elab.Tactic.Omega
/-!
# Local regularity criteria for the actual displacement
Source: independently derived continuation of the user's four - criteria paper,
4 November 2026. The square relation and sublinearity are inherited unconditional
providers. Local test vanishing and first - difference convergence remain OPEN
arithmetic obligations. The conditional consumers conclude Mathlib's RH using
the existing displacement - boundedness bridge; no reverse RH provider is assumed.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreePrimeLocalTests
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity
open RiemannResearch.NumberTheory.PrimeMultiplierRigidity

def TwoSelectedTests : Prop :=
  ∀ n, 2 ≤ n → ∃ p l : ℕ,
    p.Prime ∧ p ∣ n ∧ n ^ 2 < l ∧
    localTest (qSequence displacement) p n = 0 ∧
    localTest (qSequence displacement) l n = 0

theorem displacement_constant_of_two_selected_tests (ht : TwoSelectedTests) :
    ∀ n, 1 ≤ n → qSequence displacement n = qSequence displacement 1 := by
  apply constant_of_two_selected_tests _ _ ht
  intro n hn
  exact QSquarefreeMultiplierRigidity.closure_difference_square displacement_mem n hn

theorem riemannHypothesis_of_two_selected_tests (ht : TwoSelectedTests) : RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_bounded |qSequence displacement 1|
  intro n
  cases n with
  | zero => simpa only [qSequence_zero, abs_zero] using abs_nonneg (qSequence displacement 1)
  | succ k => rw [displacement_constant_of_two_selected_tests ht (k + 1) (by omega)]

open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity
open RiemannResearch.NumberTheory.SquareDifferenceRigidity

def WeightedLocalTests : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (n : ℝ) ^ 2 * qSequence displacement (n ^ 2) -
    ((n : ℝ) ^ 2 - 1) * qSequence displacement (n ^ 2 - 1) -
    (n : ℝ) * qSequence displacement n +
    ((n : ℝ) - 1) * qSequence displacement (n - 1) = 0

theorem displacement_constant_of_weighted_local_tests (ht : WeightedLocalTests) :
    ∀ n, 1 ≤ n → qSequence displacement n = qSequence displacement 1 := by
  apply constant_of_one_weighted_test _ (qSequence_div_nat_tendsto_zero displacement) _ ht
  intro n hn
  exact QSquarefreeMultiplierRigidity.closure_difference_square displacement_mem n hn

theorem riemannHypothesis_of_weighted_local_tests (ht : WeightedLocalTests) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_bounded |qSequence displacement 1|
  intro n
  cases n with
  | zero => simpa only [qSequence_zero, abs_zero] using abs_nonneg (qSequence displacement 1)
  | succ k => rw [displacement_constant_of_weighted_local_tests ht (k + 1) (by omega)]

open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity
open RiemannResearch.NumberTheory.SquareDifferenceRigidity

theorem riemannHypothesis_of_difference_tendsto_zero
    (hdiff : Tendsto (fun n : ℕ =>
      qSequence displacement n - qSequence displacement (n - 1)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hc := constant_of_difference_tendsto_zero (qSequence displacement)
    (fun n hn => QSquarefreeMultiplierRigidity.closure_difference_square
      displacement_mem n hn) hdiff
  apply riemannHypothesis_of_displacement_bounded |qSequence displacement 1|
  intro n
  cases n with
  | zero => simpa only [qSequence_zero, abs_zero] using abs_nonneg (qSequence displacement 1)
  | succ k => rw [hc (k + 1) (by omega)]

end RiemannResearch.RH.QSquarefreePrimeLocalTests
