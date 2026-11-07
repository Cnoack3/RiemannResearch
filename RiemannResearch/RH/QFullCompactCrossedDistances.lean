/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullCrossedDistances
import RiemannResearch.RH.QParetoSquareRootCompactness
import RiemannResearch.RH.QFullCofinalHarmonic
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QParetoSquareRootEnergy
import RiemannResearch.RH.QParetoIsometricTransport
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Crossed distances under bounded coordinate convergence

Source: CrossedDistanceLeanHandoff20261106.md, Priority 2. Compact smoothing
and the exact common-target identities replace strong convergence by bounded
coordinatewise convergence for legal approximants. The complete crossed
budget converges to its value at the actual displacement. Its vanishing is
still an explicit Open provider in the conditional RH reduction.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QFullCrossedDistances
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoIsometricTransport QFullResidueProjection QFullDisplacement

theorem forwardDistance_tendsto_of_bounded_coordinates
    {G : ℕ → QHilbert} {f : QHilbert} (hf : f ∈ closure)
    (hlegal : ∀ M, G M ∈ closure) (C : ℝ) (hbound : ∀ M, ‖G M‖ ≤ C)
    (hcoord : ∀ n, Tendsto (fun M => G M n) atTop (𝓝 (f n))) :
    Tendsto (fun M => forwardDistance (G M)) atTop (𝓝 (forwardDistance f)) := by
  have hJ := rootDefect_tendsto_of_bounded_coordinates C hbound hcoord
  have h := ((Metric.continuous_infDist_pt (paretoClosure : Set ThresholdHilbert)).comp
    A.continuous).continuousAt.tendsto.comp hJ
  convert h using 1
  · ext M
    exact forwardDistance_eq_rootDefect (G M) (hlegal M)
  · simp only [forwardDistance_eq_rootDefect f hf, Function.comp_def]

theorem inverseDistance_tendsto_of_bounded_coordinates
    {G : ℕ → QHilbert} {f : QHilbert} (hf : f ∈ closure)
    (hlegal : ∀ M, G M ∈ closure) (C : ℝ) (hbound : ∀ M, ‖G M‖ ≤ C)
    (hcoord : ∀ n, Tendsto (fun M => G M n) atTop (𝓝 (f n))) :
    Tendsto (fun M => inverseDistance (G M)) atTop (𝓝 (inverseDistance f)) := by
  have hJ := rootDefect_tendsto_of_bounded_coordinates C hbound hcoord
  have h := ((Metric.continuous_infDist_pt (closure : Set QHilbert)).continuousAt.tendsto.comp hJ
    ).const_mul (Real.sqrt zetaTwo)
  convert h using 1
  · ext M
    exact inverseDistance_eq_rootDefect (G M) (hlegal M)
  · rw [inverseDistance_eq_rootDefect f hf]

theorem crossedBudget_tendsto_of_bounded_coordinates
    {G : ℕ → QHilbert} {f : QHilbert} (hf : f ∈ closure)
    (hlegal : ∀ M, G M ∈ closure) (C : ℝ) (hbound : ∀ M, ‖G M‖ ≤ C)
    (hcoord : ∀ n, Tendsto (fun M => G M n) atTop (𝓝 (f n))) :
    Tendsto (fun M => crossedBudget (G M)) atTop (𝓝 (crossedBudget f)) :=
  ((forwardDistance_tendsto_of_bounded_coordinates hf hlegal C hbound hcoord).const_mul
    ‖toPareto pResidual‖).add
    ((inverseDistance_tendsto_of_bounded_coordinates hf hlegal C hbound hcoord).const_mul
      ‖qResidual‖)

/-- Conditional reduction: complete budget decay is still the open provider. -/
theorem displacement_eq_zero_iff_budget_of_bounded_coordinates
    {G : ℕ → QHilbert}
    (hlegal : ∀ M, G M ∈ closure) (C : ℝ) (hbound : ∀ M, ‖G M‖ ≤ C)
    (hcoord : ∀ n, Tendsto (fun M => G M n) atTop (𝓝 (displacement n))) :
    displacement = 0 ↔ Tendsto (fun M => crossedBudget (G M)) atTop (𝓝 0) := by
  have h := crossedBudget_tendsto_of_bounded_coordinates
    displacement_mem hlegal C hbound hcoord
  constructor
  · intro hd
    simpa only [hd, crossedBudget_zero] using h
  · intro hz
    exact displacement_eq_zero_of_budget_zero (tendsto_nhds_unique h hz)

theorem riemannHypothesis_of_bounded_coordinate_budget
    {G : ℕ → QHilbert}
    (hlegal : ∀ M, G M ∈ closure) (C : ℝ) (hbound : ∀ M, ‖G M‖ ≤ C)
    (hcoord : ∀ n, Tendsto (fun M => G M n) atTop (𝓝 (displacement n)))
    (hzero : Tendsto (fun M => crossedBudget (G M)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_displacement_eq_zero
    ((displacement_eq_zero_iff_budget_of_bounded_coordinates
      hlegal C hbound hcoord).mpr hzero)

end RiemannResearch.RH.QFullCrossedDistances
