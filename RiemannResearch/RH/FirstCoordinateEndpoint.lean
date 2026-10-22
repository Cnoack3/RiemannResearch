/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RealCofinalLimits
import RiemannResearch.RH.FiniteDyadicDefect
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoCoordinateBounds
import Mathlib.Tactic.Linarith

/-!
# The critical first-coordinate energy budget

Source: continuation of Christian Noack's Pareto parity research agenda,
13 October 2026. The exact normalized-dilation identity is reused from
FiniteDyadicDefect. Keeping its first-coordinate contribution proves a
quadratic strengthening and shows that the coefficient 2-sqrt(2), including
equality, is a sufficient endpoint. The actual cofinal arithmetic budget
remains an Open conditional research input. No proof of RH is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
set_option backward.isDefEq.respectTransparency false

theorem normalized_dyadic_mismatch_first (x y : ThresholdHilbert) :
    hilbertSequence (x - (Real.sqrt 2 / 2) • doubleDilation y) 1 =
      hilbertSequence x 1 := by
  have hd : hilbertSequence (doubleDilation y) 1 = 0 := by
    change hilbertSequence (hilbertDilation 2 (by decide) y) 1 = 0
    rw [hilbertDilation_sequence]
    simp [dilation]
  change hilbertSequenceLinear (x - _) 1 = _
  rw [map_sub, map_smul]
  change hilbertSequence x 1 - (Real.sqrt 2 / 2) *
    hilbertSequence (doubleDilation y) 1 = hilbertSequence x 1
  rw [hd, mul_zero, sub_zero]

theorem normalized_dyadic_mismatch_first_sq_le (x y : ThresholdHilbert) :
    (hilbertSequence x 1) ^ 2 ≤
      2 * ‖x - (Real.sqrt 2 / 2) • doubleDilation y‖ ^ 2 := by
  have h := hilbertSequence_sq_le_norm_sq
    (x - (Real.sqrt 2 / 2) • doubleDilation y) 1
  rw [normalized_dyadic_mismatch_first] at h
  norm_num at h
  exact h

theorem firstCoordinate_energy_quadratic_lower :
    (2 - Real.sqrt 2) * limitEnergy +
      (Real.sqrt 2 / 4) * (hilbertSequence limitResidual 1) ^ 2 ≤
        hilbertSequence limitResidual 1 := by
  have he := firstCoordinate_eq_energy_add_dyadicRemainder
  have hb := mul_le_mul_of_nonneg_left
    (normalized_dyadic_mismatch_first_sq_le limitResidual limitResidual)
    (show 0 ≤ Real.sqrt 2 / 4 by positivity)
  linarith

/-- A strict detector gap whenever the closed residual is nonzero. -/
theorem firstCoordinate_energy_strict_of_residual_ne_zero
    (h : limitResidual ≠ 0) :
    (2 - Real.sqrt 2) * limitEnergy < hilbertSequence limitResidual 1 := by
  have ht : hilbertSequence limitResidual 1 ≠ 0 := fun hz =>
    h (firstCoordinate_zero_iff_residual_zero.mp hz)
  have hp : 0 < (Real.sqrt 2 / 4) * (hilbertSequence limitResidual 1) ^ 2 :=
    mul_pos (by positivity) (sq_pos_of_ne_zero ht)
  linarith [firstCoordinate_energy_quadratic_lower]

/-- The finite same-stage correction is retained exactly. -/
theorem finite_firstCoordinate_quadratic_lower (n : ℕ) :
    (2 - Real.sqrt 2) * energy n +
      (Real.sqrt 2 / 4) * (hilbertSequence (projectionResidual n) 1) ^ 2 ≤
        hilbertSequence (projectionResidual n) 1 + finiteDyadicDefect n := by
  have he := finite_firstCoordinate_eq_dyadicSquare_sub_defect n
  rw [finiteDyadicSquare_eq_energy_add_remainder] at he
  have hb := mul_le_mul_of_nonneg_left
    (normalized_dyadic_mismatch_first_sq_le (projectionResidual n) (projectionResidual n))
    (show 0 ≤ Real.sqrt 2 / 4 by positivity)
  change (Real.sqrt 2 / 4) * _ ≤
    (Real.sqrt 2 / 4) * (2 * finiteDyadicResidualRemainder n) at hb
  linarith


end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

set_option backward.isDefEq.respectTransparency false
open RiemannResearch.Analysis

theorem limitResidual_first_eq_one_sub_projection :
    hilbertSequence limitResidual 1 = 1 - hilbertSequence limitProjection 1 := by
  change hilbertSequenceLinear (hilbertOne - limitProjection) 1 = _
  rw [map_sub]
  change hilbertSequence hilbertOne 1 - hilbertSequence limitProjection 1 = _
  rw [hilbertOne_sequence]
  simp [zeroAnchor]

theorem one_sub_projection_first_tendsto :
    Tendsto (fun n => 1 - hilbertSequence (projection n) 1) atTop
      (𝓝 (hilbertSequence limitResidual 1)) := by
  rw [limitResidual_first_eq_one_sub_projection]
  exact tendsto_const_nhds.sub projection_firstCoordinate_tendsto

/-- The Cauchy--Schwarz endpoint itself forces vanishing: equality in the
normalized dilation square makes the first coordinate zero. -/
theorem limitResidual_zero_of_firstCoordinate_le_sharp_energy
    (h : hilbertSequence limitResidual 1 ≤ (2 - Real.sqrt 2) * limitEnergy) :
    limitResidual = 0 := by
  have hid := firstCoordinate_eq_energy_add_dyadicRemainder
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hn : ‖limitResidual - (Real.sqrt 2 / 2) •
      doubleDilation limitResidual‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖limitResidual - (Real.sqrt 2 / 2) •
      doubleDilation limitResidual‖]
  have hv : limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hd : hilbertSequence (doubleDilation limitResidual) 1 = 0 := by
    change hilbertSequence (hilbertDilation 2 (by decide) limitResidual) 1 = 0
    rw [hilbertDilation_sequence]
    simp [dilation, hilbertSequence_zero]
  have hv1 := congrArg (fun f : ThresholdHilbert => hilbertSequence f 1) hv
  change hilbertSequenceLinear (_ - _) 1 = hilbertSequenceLinear 0 1 at hv1
  rw [map_sub, map_smul, map_zero] at hv1
  change hilbertSequence limitResidual 1 -
    (Real.sqrt 2 / 2) * hilbertSequence (doubleDilation limitResidual) 1 = 0 at hv1
  rw [hd, mul_zero, sub_zero] at hv1
  exact firstCoordinate_zero_iff_residual_zero.mp hv1

/-- The original one-sided first-projection criterion, in a cofinal form. -/
theorem projection_cofinal_lower_iff_residual_zero :
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      1 - ε ≤ hilbertSequence (projection n) 1) ↔ limitResidual = 0 := by
  constructor
  · intro h
    have hup : hilbertSequence limitResidual 1 ≤ 0 := by
      apply limit_le_of_cofinal_le_add one_sub_projection_first_tendsto
      intro ε hε N
      obtain ⟨n, hn, hp⟩ := h ε hε N
      exact ⟨n, hn, by linarith⟩
    exact firstCoordinate_zero_iff_residual_zero.mp
      (le_antisymm hup firstCoordinate_nonneg)
  · intro h ε hε N
    have hf := projection_firstCoordinate_tendsto_one_iff.mpr h
    obtain ⟨K, hK⟩ := eventually_atTop.1
      (hf.eventually_const_lt (show 1 - ε < (1 : ℝ) by linarith))
    exact ⟨max N K, le_max_left _ _, le_of_lt (hK _ (le_max_right _ _))⟩

theorem riemannHypothesis_of_projection_cofinal_lower
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      1 - ε ≤ hilbertSequence (projection n) 1) : RiemannHypothesis := by
  apply riemannHypothesis_of_firstCoordinate_zero
  exact firstCoordinate_zero_iff_residual_zero.mpr
    (projection_cofinal_lower_iff_residual_zero.mp h)

/-- A weaker sufficient condition allows an endpoint fraction of the actual
finite energy on the right. The original manuscript used theta < 1/2;
this theorem allows theta = 2 - sqrt 2, including the endpoint. -/
theorem projection_cofinal_endpoint_budget_iff_residual_zero :
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      1 - hilbertSequence (projection n) 1 ≤
        (2 - Real.sqrt 2) * energy n + ε) ↔ limitResidual = 0 := by
  have hf : Tendsto (fun n => 1 - hilbertSequence (projection n) 1 -
      (2 - Real.sqrt 2) * energy n) atTop
      (𝓝 (hilbertSequence limitResidual 1 - (2 - Real.sqrt 2) * limitEnergy)) :=
    one_sub_projection_first_tendsto.sub (energy_tendsto.const_mul _)
  constructor
  · intro h
    have hup : hilbertSequence limitResidual 1 - (2 - Real.sqrt 2) * limitEnergy ≤ 0 := by
      apply limit_le_of_cofinal_le_add hf
      intro ε hε N
      obtain ⟨n, hn, hp⟩ := h ε hε N
      exact ⟨n, hn, by linarith⟩
    apply limitResidual_zero_of_firstCoordinate_le_sharp_energy
    linarith
  · intro h
    have ht := firstCoordinate_zero_iff_residual_zero.mpr h
    have he := limitResidual_zero_iff_energy_zero.mp h
    rw [ht, he, mul_zero, sub_zero] at hf
    intro ε hε N
    obtain ⟨n, hn, hp⟩ := cofinal_le_add_of_tendsto hf ε hε N
    exact ⟨n, hn, by linarith⟩

theorem riemannHypothesis_of_projection_cofinal_endpoint_budget
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      1 - hilbertSequence (projection n) 1 ≤
        (2 - Real.sqrt 2) * energy n + ε) : RiemannHypothesis := by
  apply riemannHypothesis_of_firstCoordinate_zero
  exact firstCoordinate_zero_iff_residual_zero.mpr
    (projection_cofinal_endpoint_budget_iff_residual_zero.mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization
