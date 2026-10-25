/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreePacketCapacity
import RiemannResearch.Analysis.NormalizedSignedEnergy
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Signed correlation criteria for the actual squarefree capacity

The complete Pareto residual Gram matrix is retained. The arithmetic inputs
are explicit: positive complete energy certificates, divergence of reciprocal
mass, and a vanishing normalized signed cross budget. This module supplies
none of those last two arithmetic estimates unconditionally.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.SquarefreePacketCapacity
open Pareto RiemannResearch.Analysis

theorem reciprocalEnergyAverage_mem_stage
    (N : ℕ → ℕ) (hN : Monotone N) (F : ℕ → ThresholdHilbert)
    (hF : ∀ i, F i ∈ stage (N i)) (A : ℕ → ℝ) (m : ℕ) :
    reciprocalEnergyAverage F A m ∈ stage (N m) := by
  unfold reciprocalEnergyAverage
  apply (stage (N m)).smul_mem
  apply (stage (N m)).sum_mem
  intro i hi
  apply (stage (N m)).smul_mem
  exact stage_monotone (hN (Nat.le_of_lt (Finset.mem_range.mp hi))) (hF i)

theorem signed_cross_ge_limiting_defect
    (N : ℕ → ℕ) (hN : Monotone N) (F : ℕ → ThresholdHilbert)
    (hF : ∀ i, F i ∈ stage (N i)) (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (henergy : ∀ i, ‖F i - hilbertOne‖ ^ 2 ≤ A i) {m : ℕ} (hm : 0 < m) :
    1 - limitingCapacity - (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹ ≤
      reciprocalEnergyCross (fun i => F i - hilbertOne) A m := by
  apply reciprocalEnergyCross_ge_gap _ A hA henergy m
  rw [reciprocalEnergyAverage_sub F A hilbertOne m
    (ne_of_gt (reciprocalEnergyMass_pos A hA hm)), norm_sub_rev]
  exact limiting_error_floor (N m) (reciprocalEnergyAverage F A m)
    (reciprocalEnergyAverage_mem_stage N hN F hF A m)

/-- The signed criterion consumes actual squarefree legality. The normalized
cross budget may be much weaker than a bounded unnormalized cross sum. -/
theorem saturation_of_signed_correlation_budget
    (N : ℕ → ℕ) (hN : Monotone N) (F : ℕ → ThresholdHilbert)
    (hF : ∀ i, F i ∈ stage (N i)) (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (henergy : ∀ i, ‖F i - hilbertOne‖ ^ 2 ≤ A i) (b : ℕ → ℝ)
    (hcross : ∀ᶠ m in atTop,
      reciprocalEnergyCross (fun i => F i - hilbertOne) A m ≤ b m)
    (hbudget : Tendsto b atTop (𝓝 0))
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop) :
    Tendsto kappa atTop (𝓝 1) := by
  have hv := reciprocalEnergyAverage_tendsto_of_cross_budget
    (fun i => F i - hilbertOne) A hA henergy b hcross hbudget hmass
  have he : Tendsto (fun m =>
      ‖reciprocalEnergyAverage (fun i => F i - hilbertOne) A m‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by simpa using hv.norm.pow 2
  have hfloor : ∀ᶠ m in atTop, 1 - limitingCapacity ≤
      ‖reciprocalEnergyAverage (fun i => F i - hilbertOne) A m‖ ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [reciprocalEnergyAverage_sub F A hilbertOne m
      (ne_of_gt (reciprocalEnergyMass_pos A hA (by omega))), norm_sub_rev]
    exact limiting_error_floor (N m) (reciprocalEnergyAverage F A m)
      (reciprocalEnergyAverage_mem_stage N hN F hF A m)
  have hg : 1 - limitingCapacity ≤ 0 := ge_of_tendsto he hfloor
  apply saturation_iff_limit.mpr
  linarith [limitingCapacity_le_one]

theorem riemannHypothesis_of_signed_correlation_budget
    (N : ℕ → ℕ) (hN : Monotone N) (F : ℕ → ThresholdHilbert)
    (hF : ∀ i, F i ∈ stage (N i)) (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (henergy : ∀ i, ‖F i - hilbertOne‖ ^ 2 ≤ A i) (b : ℕ → ℝ)
    (hcross : ∀ᶠ m in atTop,
      reciprocalEnergyCross (fun i => F i - hilbertOne) A m ≤ b m)
    (hbudget : Tendsto b atTop (𝓝 0))
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop) :
    RiemannHypothesis :=
  riemannHypothesis_of_saturation
    (saturation_of_signed_correlation_budget N hN F hF A hA henergy b hcross hbudget hmass)

end RiemannResearch.RH.SquarefreePacketCapacity
