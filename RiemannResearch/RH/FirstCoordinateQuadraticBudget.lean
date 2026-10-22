/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.QuadraticDetectorBudget
import RiemannResearch.Analysis.RealCofinalLimits
import RiemannResearch.RH.FirstCoordinateEndpoint
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A quadratic allowance for the actual first-coordinate endpoint

Source: the supplied Pareto parity continuation and direct scalar deductions
from its already checked firstCoordinate_energy_quadratic_lower. The actual
cofinal optimizer upper budget remains Open. This does not prove RH.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis
set_option backward.isDefEq.respectTransparency false
def quadraticEndpointBudget (d : ℝ) : ℝ :=
  (2 - Real.sqrt 2) * d + (Real.sqrt 2 / 4) * ((2 - Real.sqrt 2) * d) ^ 2
theorem quadraticEndpointBudget_tendsto :
    Tendsto (fun n => quadraticEndpointBudget (energy n)) atTop
      (𝓝 (quadraticEndpointBudget limitEnergy)) := by
  unfold quadraticEndpointBudget
  exact (energy_tendsto.const_mul _).add
    (((energy_tendsto.const_mul _).pow 2).const_mul _)
theorem limitResidual_zero_of_firstCoordinate_le_quadratic_budget
    (h : hilbertSequence limitResidual 1 ≤ quadraticEndpointBudget limitEnergy) :
    limitResidual = 0 := by
  have hc : 0 < 2 - Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have he : 0 ≤ limitEnergy := sq_nonneg _
  apply limitResidual_zero_iff_energy_zero.mpr
  exact quadratic_detector_zero_of_budget hc (by positivity) he
    firstCoordinate_energy_quadratic_lower h
theorem firstCoordinate_gt_quadratic_budget_of_residual_ne_zero
    (h : limitResidual ≠ 0) :
    quadraticEndpointBudget limitEnergy < hilbertSequence limitResidual 1 := by
  by_contra hn
  exact h (limitResidual_zero_of_firstCoordinate_le_quadratic_budget (le_of_not_gt hn))
theorem projection_cofinal_quadratic_budget_iff_residual_zero :
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      1 - hilbertSequence (projection n) 1 ≤ quadraticEndpointBudget (energy n) + ε)
      ↔ limitResidual = 0 := by
  have hf := one_sub_projection_first_tendsto.sub quadraticEndpointBudget_tendsto
  constructor
  · intro h
    have hup : hilbertSequence limitResidual 1 - quadraticEndpointBudget limitEnergy ≤ 0 := by
      apply limit_le_of_cofinal_le_add hf
      intro ε hε N
      obtain ⟨n, hn, hp⟩ := h ε hε N
      exact ⟨n, hn, by linarith⟩
    apply limitResidual_zero_of_firstCoordinate_le_quadratic_budget
    linarith
  · intro h ε hε N
    have ht := firstCoordinate_zero_iff_residual_zero.mpr h
    have he := limitResidual_zero_iff_energy_zero.mp h
    simp only [ht, he, quadraticEndpointBudget, mul_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, sub_zero] at hf
    obtain ⟨n, hn, hp⟩ := cofinal_le_add_of_tendsto hf ε hε N
    exact ⟨n, hn, by
      dsimp only [quadraticEndpointBudget]
      linarith⟩
theorem riemannHypothesis_of_projection_cofinal_quadratic_budget
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      1 - hilbertSequence (projection n) 1 ≤ quadraticEndpointBudget (energy n) + ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_firstCoordinate_zero
  exact firstCoordinate_zero_iff_residual_zero.mpr
    (projection_cofinal_quadratic_budget_iff_residual_zero.mp h)
end RiemannResearch.RH.Pareto.CoefficientStabilization
