/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FirstCoordinateEndpoint
import RiemannResearch.RH.ResidueGramModeIdentities
import RiemannResearch.RH.ResidueOrthonormalCoordinates
import Mathlib.Tactic.Ring

/-!
# A finite mixed Gram endpoint criterion

Source: assembly of the existing full-Pareto inverse-Gram projection formulas
with FirstCoordinateEndpoint. All matrices refer to the complete infinite
Pareto norm. The cofinal lower bound for endpointGramStatistic remains Open.
No numerical computation or arbitrary approximant is used as a provider.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open TailCapacity IntegerDPP

theorem energy_eq_one_sub_inverseGram (n : ℕ) :
    energy n = 1 - dotProduct (logarithmicSource n)
      ((fullGram n)⁻¹.mulVec (logarithmicSource n)) := by
  rw [logarithmic_inverseGram_eq_mode_sum, energy_eq_one_sub_mode_sum]

/-- A single finite mixed Gram statistic with the critical energy allowance. -/
def endpointGramStatistic (n : ℕ) : ℝ :=
  dotProduct (reciprocalSource n) ((fullGram n)⁻¹.mulVec (logarithmicSource n)) -
    (2 - Real.sqrt 2) * dotProduct (logarithmicSource n)
      ((fullGram n)⁻¹.mulVec (logarithmicSource n))

theorem endpointGramStatistic_eq_projection_energy (n : ℕ) :
    endpointGramStatistic n = hilbertSequence (projection n) 1 +
      (2 - Real.sqrt 2) * energy n - (2 - Real.sqrt 2) := by
  rw [endpointGramStatistic, ← projection_firstCoordinate_eq_inverseGram,
    anchoredEvaluationCLM_apply, energy_eq_one_sub_inverseGram]
  ring

/-- Its unconditional limit retains the complete normalized-dilation square. -/
theorem endpointGramStatistic_tendsto :
    Tendsto endpointGramStatistic atTop
      (𝓝 (Real.sqrt 2 - 1 - (Real.sqrt 2 / 2) *
        ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2)) := by
  have ht := (projection_firstCoordinate_tendsto.add
    (energy_tendsto.const_mul (2 - Real.sqrt 2))).sub_const (2 - Real.sqrt 2)
  have he : hilbertSequence limitProjection 1 +
      (2 - Real.sqrt 2) * limitEnergy - (2 - Real.sqrt 2) =
      Real.sqrt 2 - 1 - (Real.sqrt 2 / 2) *
        ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2 := by
    linarith [firstCoordinate_eq_energy_add_dyadicRemainder,
      limitResidual_first_eq_one_sub_projection]
  simpa only [← endpointGramStatistic_eq_projection_energy, he] using ht

theorem endpointGram_cofinal_lower_iff_residual_zero :
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      Real.sqrt 2 - 1 - ε ≤ endpointGramStatistic n) ↔ limitResidual = 0 := by
  rw [← projection_cofinal_endpoint_budget_iff_residual_zero]
  constructor <;> intro h ε hε N
  · obtain ⟨n, hn, hb⟩ := h ε hε N
    rw [endpointGramStatistic_eq_projection_energy] at hb
    exact ⟨n, hn, by linarith⟩
  · obtain ⟨n, hn, hb⟩ := h ε hε N
    refine ⟨n, hn, ?_⟩
    rw [endpointGramStatistic_eq_projection_energy]
    linarith

theorem riemannHypothesis_of_endpointGram_cofinal_lower
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      Real.sqrt 2 - 1 - ε ≤ endpointGramStatistic n) : RiemannHypothesis := by
  apply riemannHypothesis_of_firstCoordinate_zero
  exact firstCoordinate_zero_iff_residual_zero.mpr
    (endpointGram_cofinal_lower_iff_residual_zero.mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization
