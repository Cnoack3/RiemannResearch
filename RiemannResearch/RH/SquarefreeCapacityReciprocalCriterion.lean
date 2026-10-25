/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreePacketCapacity
import RiemannResearch.Analysis.ReciprocalEnergyGap
import Mathlib.Tactic.Linarith

/-!
# Reciprocal-energy certificates for squarefree packet saturation

Source: user-requested five-attempt capacity investigation, 24 October 2026.
Every trial is in the actual finite squarefree packet span. The complete
energy estimate and reciprocal-mass cofinality remain explicit hypotheses.
This module supplies no arithmetic provider of cofinality.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.SquarefreePacketCapacity
open Pareto
open RiemannResearch.Analysis.ReciprocalEnergyGap

theorem reciprocal_mass_bound_of_deficit
    (n : ℕ) (f : ThresholdHilbert) (hf : f ∈ stage n)
    {S c : ℝ} (hgap : limitingCapacity < 1) (hS : 0 < S) (hc : 0 ≤ c)
    (herr : ‖hilbertOne - f‖ ^ 2 ≤ 1 / S + c / S ^ 2) :
    S ≤ max 1 ((1 + c) / (1 - limitingCapacity)) := by
  exact reciprocal_sum_le_max (sub_pos.mpr hgap) hS hc
    ((limiting_error_floor n f hf).trans herr)

/-- Conditional research reduction: actual legal trials with cofinal
controlled reciprocal mass force the squarefree capacity to saturate. -/
theorem saturation_of_reciprocal_trials
    (N : ℕ → ℕ) (F : ℕ → ThresholdHilbert) (S : ℕ → ℝ) (c : ℝ)
    (hlegal : ∀ i, F i ∈ stage (N i)) (hc : 0 ≤ c)
    (hS : ∀ i, 0 < S i)
    (herr : ∀ i, ‖hilbertOne - F i‖ ^ 2 ≤ 1 / S i + c / (S i) ^ 2)
    (hlarge : ∀ R : ℝ, ∃ i, R ≤ S i) :
    Tendsto kappa atTop (𝓝 1) := by
  have hz : 1 - limitingCapacity = 0 :=
    gap_eq_zero_of_reciprocal_cofinal S (sub_nonneg.mpr limitingCapacity_le_one)
      hc hS (fun i => (limiting_error_floor (N i) (F i) (hlegal i)).trans (herr i))
      hlarge
  apply saturation_iff_limit.mpr
  linarith

theorem riemannHypothesis_of_reciprocal_trials
    (N : ℕ → ℕ) (F : ℕ → ThresholdHilbert) (S : ℕ → ℝ) (c : ℝ)
    (hlegal : ∀ i, F i ∈ stage (N i)) (hc : 0 ≤ c)
    (hS : ∀ i, 0 < S i)
    (herr : ∀ i, ‖hilbertOne - F i‖ ^ 2 ≤ 1 / S i + c / (S i) ^ 2)
    (hlarge : ∀ R : ℝ, ∃ i, R ≤ S i) : RiemannHypothesis :=
  riemannHypothesis_of_saturation
    (saturation_of_reciprocal_trials N F S c hlegal hc hS herr hlarge)

end RiemannResearch.RH.SquarefreePacketCapacity
