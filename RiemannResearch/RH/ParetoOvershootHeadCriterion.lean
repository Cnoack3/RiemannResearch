/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoNegativeMassHead
import RiemannResearch.RH.ParetoProjectionOvershoot
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ParetoHilbertPhysical
import RiemannResearch.Analysis.RealCofinalLimits
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A finite arithmetic head for the actual overshoot endpoint criterion

Source: the user-directed attempt to prove the open arithmetic overshoot bound,
19 October 2026. The complete Pareto tail is bounded explicitly; the remaining
finite positive-part inequality uses the actual projection coefficients.
The cofinal arithmetic head estimate remains Open. This module does not prove
that estimate or RH. Bagchi (2006), Theorem 1, arXiv:math/0607733, supplies
background on the discrete closure criterion, not an arithmetic upper bound.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
set_option backward.isDefEq.respectTransparency false

def projectionOvershootHead (H n : ℕ) : ℝ :=
  negativeMassHead H (projectionResidual n)

/-- A genuinely finite positive-part sum for the actual optimizer. -/
theorem projectionOvershootHead_eq_sum (H n : ℕ) :
    projectionOvershootHead H n =
      ∑ k ∈ Finset.range H, paretoWeight k *
        max (hilbertSequence (projection n) (k + 1) - 1) 0 := by
  rw [projectionOvershootHead, negativeMassHead_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hs := congrFun (hilbertSequence_sub hilbertOne (projection n)) (k + 1)
  simp only [Pi.sub_apply] at hs
  have he : hilbertSequence hilbertOne (k + 1) = 1 := by
    rw [hilbertOne_sequence]
    simp [zeroAnchor]
  change paretoWeight k * max (-hilbertSequence (hilbertOne - projection n) (k + 1)) 0 = _
  rw [hs, he]
  congr 2
  ring

private theorem residual_norm_le_one (n : ℕ) : ‖projectionResidual n‖ ≤ 1 := by
  have ho := projectionResidual_inner_mem n (projection n)
    ((finiteSpace n).starProjection_apply_mem _)
  rw [projectionResidual, inner_sub_left, real_inner_self_eq_norm_sq] at ho
  have hs := norm_sub_sq_real hilbertOne (projection n)
  rw [hilbertOne_norm_sq] at hs
  change ‖projectionResidual n‖ ^ 2 =
    1 - 2 * inner ℝ hilbertOne (projection n) + ‖projection n‖ ^ 2 at hs
  nlinarith [sq_nonneg ‖projection n‖, norm_nonneg (projectionResidual n)]

/-- The whole omitted tail, with its actual residual energy retained. -/
theorem projectionOvershoot_head_bounds (H n : ℕ) :
    projectionOvershootHead H n ≤ projectionOvershoot n ∧
      projectionOvershoot n ≤ projectionOvershootHead H n +
        ‖projectionResidual n‖ * Real.sqrt (1 / ((H : ℝ) + 1)) := by
  constructor
  · exact negativeMassHead_le H (projectionResidual n)
  · exact negativeMassHead_truncation_upper H (projectionResidual n)

private theorem tail_allowance_tendsto_zero :
    Tendsto (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [Real.sqrt_zero, Function.comp_def] using
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h

/-- The finite diagonal heads converge to the complete limiting overshoot. -/
theorem projectionOvershootHead_diagonal_tendsto :
    Tendsto (fun n => projectionOvershootHead n n) atTop (𝓝 limitOvershoot) := by
  have hz : Tendsto (fun n => projectionOvershoot n - projectionOvershootHead n n)
      atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => sub_nonneg.mpr (projectionOvershoot_head_bounds n n).1) _
      tail_allowance_tendsto_zero
    intro n
    have hb := (projectionOvershoot_head_bounds n n).2
    have hm := mul_le_mul_of_nonneg_right (residual_norm_le_one n)
      (Real.sqrt_nonneg (1 / ((n : ℝ) + 1)))
    linarith
  simpa only [sub_sub_cancel, sub_zero] using projectionOvershoot_tendsto.sub hz

/-- Conditional research reduction. Only the finite arithmetic head budget
is assumed; the infinite tail and passage to the actual limit are discharged. -/
theorem projectionOvershootHead_cofinal_endpoint_iff_residual_zero :
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      projectionOvershootHead n n ≤ (1 - Real.sqrt 2 / 2) * energy n + ε) ↔
      limitResidual = 0 := by
  constructor
  · intro h
    have ht := projectionOvershootHead_diagonal_tendsto.sub
      (energy_tendsto.const_mul (1 - Real.sqrt 2 / 2))
    have hl : limitOvershoot - (1 - Real.sqrt 2 / 2) * limitEnergy ≤ 0 := by
      apply RiemannResearch.Analysis.limit_le_of_cofinal_le_add ht
      intro ε hε N
      obtain ⟨n, hn, hb⟩ := h ε hε N
      exact ⟨n, hn, by linarith⟩
    apply projectionOvershoot_cofinal_endpoint_iff_residual_zero.mp
    have hf := projectionOvershoot_tendsto.sub
      (energy_tendsto.const_mul (1 - Real.sqrt 2 / 2))
    intro ε hε N
    obtain ⟨n, hn, hb⟩ :=
      RiemannResearch.Analysis.cofinal_le_add_of_tendsto hf ε hε N
    exact ⟨n, hn, by linarith⟩
  · intro h ε hε N
    obtain ⟨n, hn, hb⟩ :=
      projectionOvershoot_cofinal_endpoint_iff_residual_zero.mpr h ε hε N
    exact ⟨n, hn, (projectionOvershoot_head_bounds n n).1.trans hb⟩

theorem riemannHypothesis_of_projectionOvershootHead_cofinal_endpoint
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      projectionOvershootHead n n ≤ (1 - Real.sqrt 2 / 2) * energy n + ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_projectionOvershoot_cofinal_endpoint
  exact projectionOvershoot_cofinal_endpoint_iff_residual_zero.mpr
    (projectionOvershootHead_cofinal_endpoint_iff_residual_zero.mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization
