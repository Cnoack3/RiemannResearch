/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusFixedHeadLimit
import RiemannResearch.Analysis.SingleObservationProjection

/-!
# Exact first-head capacity as a projection defect

Source: user-provided Single Head Duality handoff, Section 14, for the actual
complete-tail capacity and the first-head target. The standard one-observation
projection minimum identifies the capacity exactly, including its conductor
limit and the exact decrement of the projection error. The limiting defect
is not asserted to vanish.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem inner_singleHeadIndicator (x : ThresholdHilbert) :
    inner ℝ x (finiteHeadIndicator 1) = (1 / 2 : ℝ) * hilbertSequence x 1 := by
  simp only [finiteHeadIndicator, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [inner_paretoPoint]
  change paretoWeight 0 * hilbertSequence x 1 = _
  norm_num [paretoWeight]

theorem singleHeadProjection_norm_sq_pos (S : Submodule ℝ ThresholdHilbert)
    [S.HasOrthogonalProjection] (hu : canonicalMobiusHilbert 1 ∈ S) :
    0 < ‖S.starProjection (finiteHeadIndicator 1)‖ ^ 2 := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  have ho := (S.mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal (finiteHeadIndicator 1)) _ hu
  rw [hz, sub_zero, inner_singleHeadIndicator,
    canonicalMobiusHilbert_exact 1 1 (by omega) (by omega)] at ho
  norm_num at ho

def singleHeadError (M : ℕ) : ℝ :=
  ‖finiteHeadIndicator 1 - (finiteSpace M).starProjection (finiteHeadIndicator 1)‖ ^ 2

def singleHeadLimitError : ℝ :=
  ‖finiteHeadIndicator 1 - closedSpace.starProjection (finiteHeadIndicator 1)‖ ^ 2

theorem singleHeadError_tendsto :
    Tendsto singleHeadError atTop (𝓝 singleHeadLimitError) :=
  RiemannResearch.Analysis.ExhaustiveWalk.walkError_tendsto residueAtom id
    Function.surjective_id (finiteHeadIndicator 1)

theorem singleHeadLimitError_eq_zero_iff_density :
    singleHeadLimitError = 0 ↔ closedSpace = ⊤ := by
  exact (RiemannResearch.Analysis.ExhaustiveWalk.limitingError_eq_zero_iff
    residueAtom (finiteHeadIndicator 1)).trans (finiteHeadIndicator_mem_iff_density 1 (by omega))

namespace SignedCovariance
open RiemannResearch.Analysis.SingleObservationProjection

theorem singleHead_full_minimum (M : ℕ) (hM : 1 ≤ M) :
    (1 / 2 : ℝ) + (windowCapacity 1 M (by omega))⁻¹ =
      (1 / 4 : ℝ) / ‖(finiteSpace M).starProjection (finiteHeadIndicator 1)‖ ^ 2 := by
  have hu : canonicalMobiusHilbert 1 ∈ finiteSpace M :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hM
      (canonicalMobiusHilbert_mem_finiteSpace 1)
  have hq := singleHeadProjection_norm_sq_pos (finiteSpace M) hu
  have hp := observation_energy_isLeast (finiteSpace M) (finiteHeadIndicator 1)
    (1 / 2 : ℝ) (ne_of_gt hq)
  have hset : {b : ℝ | ∃ x : ThresholdHilbert, x ∈ finiteSpace M ∧
      inner ℝ (finiteHeadIndicator 1) x = (1 / 2 : ℝ) ∧ ‖x‖ ^ 2 = b} =
      {b : ℝ | ∃ x : ThresholdHilbert, x ∈ finiteSpace M ∧
      (∀ j : ℕ, 0 < j → j ≤ 1 → hilbertSequence x j = 1) ∧ ‖x‖ ^ 2 = b} := by
    ext b
    constructor
    · rintro ⟨x, hx, ho, he⟩
      refine ⟨x, hx, ?_, he⟩
      intro j hj hj1
      have hj' : j = 1 := by omega
      subst j
      rw [real_inner_comm, inner_singleHeadIndicator] at ho
      linarith
    · rintro ⟨x, hx, hh, he⟩
      refine ⟨x, hx, ?_, he⟩
      rw [real_inner_comm, inner_singleHeadIndicator, hh 1 (by omega) (by omega)]
      ring
  rw [hset] at hp
  have hm := canonicalWindow_full_isLeast_all_legal 1 M (by omega) hM
  have he := hm.unique hp
  norm_num only [Nat.cast_one, one_add_one_eq_two, show (1 / 2 : ℝ)^2 = 1 / 4 by norm_num] at he
  exact he

/-- Exact arithmetic capacity equals the reciprocal first-coordinate projection defect. -/
theorem singleHeadError_eq_inv_capacity_add_two (M : ℕ) (hM : 1 ≤ M) :
    singleHeadError M = (windowCapacity 1 M (by omega) + 2)⁻¹ := by
  have hu : canonicalMobiusHilbert 1 ∈ finiteSpace M :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hM
      (canonicalMobiusHilbert_mem_finiteSpace 1)
  have hq := singleHeadProjection_norm_sq_pos (finiteSpace M) hu
  have hk : 0 < windowCapacity 1 M (by omega) := capacity_pos _ _ _
  have he := singleHead_full_minimum M hM
  have hne := ne_of_gt hq
  have hpn : ‖(finiteSpace M).starProjection (finiteHeadIndicator 1)‖ ≠ 0 :=
    fun h => hne (by rw [h]; norm_num)
  have hkne := ne_of_gt hk
  have hkn : windowCapacity 1 M (by omega) + 2 ≠ 0 := by positivity
  have he' : 2 * ‖(finiteSpace M).starProjection (finiteHeadIndicator 1)‖ ^ 2 *
      (windowCapacity 1 M (by omega) + 2) = windowCapacity 1 M (by omega) := by
    field_simp [hpn, hkne] at he
    nlinarith [he]
  unfold singleHeadError
  rw [projection_defect_energy, finiteHeadIndicator_norm_sq]
  norm_num only [Nat.cast_one, one_add_one_eq_two]
  rw [← one_div]
  apply (eq_div_iff hkn).mpr
  nlinarith [he']

theorem singleHeadError_pos (M : ℕ) (hM : 1 ≤ M) : 0 < singleHeadError M := by
  rw [singleHeadError_eq_inv_capacity_add_two M hM]
  have hk : 0 < windowCapacity 1 M (by omega) := capacity_pos _ _ _
  exact inv_pos.mpr (by linarith)

theorem singleHeadCapacity_limit_of_not_density (hd : closedSpace ≠ ⊤) :
    Tendsto (fun M => windowCapacity 1 M (by omega)) atTop
      (𝓝 (singleHeadLimitError⁻¹ - 2)) := by
  have ht : singleHeadLimitError ≠ 0 :=
    fun h => hd (singleHeadLimitError_eq_zero_iff_density.mp h)
  have hlim := (singleHeadError_tendsto.inv₀ ht).sub_const 2
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  rw [singleHeadError_eq_inv_capacity_add_two M hM, inv_inv]
  ring

theorem singleHeadNormal_limit_energy (Z : ThresholdHilbert)
    (hlim : Tendsto (fun M => windowNormal 1 M (by omega)) atTop (𝓝 Z))
    (hd : closedSpace ≠ ⊤) :
    ‖Z‖ ^ 2 = singleHeadLimitError⁻¹ - 2 := by
  have hc : Tendsto (fun M => windowCapacity 1 M (by omega)) atTop (𝓝 (‖Z‖ ^ 2)) := by
    simpa only [windowNormal_energy] using hlim.norm.pow 2
  exact tendsto_nhds_unique hc (singleHeadCapacity_limit_of_not_density hd)

theorem singleHeadError_succ_drop (M : ℕ) (hM : 1 ≤ M) :
    singleHeadError M - singleHeadError (M + 1) =
      windowGain 1 M (by omega) /
        ((windowCapacity 1 M (by omega) + 2) *
          (windowCapacity 1 (M + 1) (by omega) + 2)) := by
  rw [singleHeadError_eq_inv_capacity_add_two M hM,
    singleHeadError_eq_inv_capacity_add_two (M + 1) (by omega)]
  have h0 : windowCapacity 1 M (by omega) + 2 ≠ 0 := by
    have hc : 0 < windowCapacity 1 M (by omega) := capacity_pos _ _ _
    linarith
  have h1 : windowCapacity 1 (M + 1) (by omega) + 2 ≠ 0 := by
    have hc : 0 < windowCapacity 1 (M + 1) (by omega) := capacity_pos _ _ _
    linarith
  have he := windowCapacity_succ 1 M (by omega) hM
  field_simp [h0, h1]
  linarith

end SignedCovariance
end RiemannResearch.RH.Pareto.CoefficientStabilization
