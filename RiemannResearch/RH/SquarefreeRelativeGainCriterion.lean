/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreePacketCapacity
import RiemannResearch.Analysis.RelativeGainSaturation
import RiemannResearch.Analysis.ResidualGainProduct

/-!
# Relative-gain criterion for the actual squarefree capacities

Source: the inverse-Schur proposal in the user's 24 October 2026 handoff.
All capacities below are the actual complete-Pareto Gram capacities.
The block lower bound and cofinal mass remain explicit hypotheses.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.SquarefreePacketCapacity
open RiemannResearch.Analysis.RelativeGainSaturation

def relativeGain (j : ℕ) : ℝ := exactGain kappa j

theorem relativeGain_bounds (j : ℕ) : 0 ≤ relativeGain j ∧ relativeGain j < 1 :=
  exactGain_bounds kappa_monotone (fun n => (kappa_bounds n).2) j

theorem relativeGain_exact (j : ℕ) :
    relativeGain j * (1 - kappa j) = kappa (j + 1) - kappa j :=
  exactGain_mul_deficit (fun n => (kappa_bounds n).2) j

theorem defect_product_exact (N : ℕ) :
    1 - kappa N = (1 - kappa 0) * ∏ j ∈ Finset.range N, (1 - relativeGain j) :=
  defect_eq_product (fun n => (kappa_bounds n).2) N

theorem relative_mass_deficit_bound (N : ℕ) :
    (1 - limitingCapacity) * mass relativeGain N ≤ limitingCapacity - kappa 0 :=
  limiting_mass_deficit_le kappa_monotone (fun j => (relativeGain_bounds j).1)
    (fun j => (relativeGain_exact j).le) kappa_le_limit N

/-- A positive limiting defect bounds every partial relative-gain mass. -/
theorem relative_mass_bound_of_deficit (hgap : limitingCapacity < 1) (N : ℕ) :
    mass relativeGain N ≤ (limitingCapacity - kappa 0) / (1 - limitingCapacity) := by
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  simpa [mul_comm] using relative_mass_deficit_bound N

/-- The selected cutoffs may advance by arbitrary finite squarefree blocks. -/
theorem saturation_of_relative_block_gains
    (N : ℕ → ℕ) (hN : Monotone N) (b : ℕ → ℝ)
    (hb : ∀ j, 0 ≤ b j)
    (hgain : ∀ j, b j * (1 - kappa (N j)) ≤
      kappa (N (j + 1)) - kappa (N j))
    (hlarge : ∀ R : ℝ, ∃ M, R ≤ mass b M) :
    Tendsto kappa atTop (𝓝 1) := by
  apply saturation_iff_limit.mpr
  exact upper_eq_one_of_cofinal_mass (kappa_monotone.comp hN) hb hgain
    (fun j => kappa_le_limit (N j)) limitingCapacity_le_one hlarge

theorem riemannHypothesis_of_relative_block_gains
    (N : ℕ → ℕ) (hN : Monotone N) (b : ℕ → ℝ)
    (hb : ∀ j, 0 ≤ b j)
    (hgain : ∀ j, b j * (1 - kappa (N j)) ≤
      kappa (N (j + 1)) - kappa (N j))
    (hlarge : ∀ R : ℝ, ∃ M, R ≤ mass b M) : RiemannHypothesis :=
  riemannHypothesis_of_saturation
    (saturation_of_relative_block_gains N hN b hb hgain hlarge)

theorem saturation_of_cofinal_relative_mass
    (hlarge : ∀ R : ℝ, ∃ N, R ≤ mass relativeGain N) :
    Tendsto kappa atTop (𝓝 1) := by
  apply saturation_iff_limit.mpr
  exact upper_eq_one_of_cofinal_mass kappa_monotone
    (fun j => (relativeGain_bounds j).1) (fun j => (relativeGain_exact j).le)
    kappa_le_limit limitingCapacity_le_one hlarge

/-- Exact equivalence, reusing the existing generic residual-product theorem. -/
theorem saturation_iff_relativeGain_not_summable :
    Tendsto kappa atTop (𝓝 1) ↔ ¬Summable relativeGain := by
  have he : Tendsto (fun n => 1 - kappa n) atTop (𝓝 0) ↔
      ¬Summable relativeGain :=
    RiemannResearch.Analysis.ResidualGain.residual_tendsto_zero_iff_not_summable
      (sub_pos.mpr (kappa_bounds 0).2)
      (fun j => (relativeGain_bounds j).1) (fun j => (relativeGain_bounds j).2)
      (fun j => defect_succ_eq (fun n => (kappa_bounds n).2) j)
  have hl : Tendsto (fun n => 1 - kappa n) atTop (𝓝 (1 - limitingCapacity)) :=
    tendsto_const_nhds.sub kappa_tendsto
  have hz : Tendsto (fun n => 1 - kappa n) atTop (𝓝 0) ↔ limitingCapacity = 1 := by
    constructor
    · intro h
      have hzero := tendsto_nhds_unique hl h
      linarith
    · intro h
      simpa only [h, sub_self] using hl
  exact saturation_iff_limit.trans (hz.symm.trans he)

theorem riemannHypothesis_of_relativeGain_not_summable
    (h : ¬Summable relativeGain) : RiemannHypothesis :=
  riemannHypothesis_of_saturation (saturation_iff_relativeGain_not_summable.mpr h)

end RiemannResearch.RH.SquarefreePacketCapacity
