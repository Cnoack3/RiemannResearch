/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullCofinalHarmonic
import RiemannResearch.RH.QShiftedReciprocalBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Reciprocal limits and full-conductor projection commutation

Source: the user's compactness and projection-commutation argument,
6 November 2026. The operator called R in the discussion is
QShiftedReciprocal.B in the source. The closure and displacement below
use every integer conductor. No squarefree displacement is substituted.

Continuity preserves the limit Rd; it does not force that limit to vanish.
The additional vanishing projection defect is an explicit open hypothesis
in the RH reduction. A nonzero vector with decaying reciprocal iterates
is exhibited to isolate the invalid general zero-limit inference.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QFullReciprocalLimits
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QShiftedReciprocal QFullResidueProjection QFullDisplacement

/-- Bounded linear continuity transports the actual limit, which need not be zero. -/
theorem reciprocal_tendsto {G : ℕ → QHilbert} {f : QHilbert}
    (h : Tendsto G atTop (𝓝 f)) :
    Tendsto (fun M => B (G M)) atTop (𝓝 (B f)) :=
  (B.continuous.tendsto f).comp h

/-- Division by a positive coordinate multiplier is injective. -/
theorem reciprocal_eq_zero_iff (f : QHilbert) : B f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply B_faithful f
    rw [h, inner_zero_right]
  · intro h
    simp [h]

/-- The constant target has a nonzero reciprocal image. -/
theorem reciprocal_qOne_ne_zero : B qOne ≠ 0 := by
  intro h
  have he := (reciprocal_eq_zero_iff qOne).mp h
  have hn := qOne_norm
  rw [he, norm_zero] at hn
  norm_num at hn

/-- A fixed-point identity would force zero; membership in H does not. -/
theorem reciprocal_fixed_point_iff (f : QHilbert) : B f = f ↔ f = 0 := by
  constructor
  · intro h
    have hn := B_norm_le_half f
    rw [h] at hn
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg f])
  · intro h
    simp [h]

/-- Self-adjoint reciprocal multiplication commutes with a projection iff its range is invariant. -/
theorem reciprocal_commutes_iff_invariant (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] :
    (∀ f, S.starProjection (B f) = B (S.starProjection f)) ↔
      (∀ f ∈ S, B f ∈ S) := by
  constructor
  · intro hc f hf
    have he := hc f
    rw [Submodule.starProjection_eq_self_iff.mpr hf] at he
    rw [← he]
    exact S.starProjection_apply_mem _
  · intro hi f
    have horth : B (f - S.starProjection f) ∈ Sᗮ := by
      apply (S.mem_orthogonal _).mpr
      intro v hv
      rw [← B_symmetric]
      exact Submodule.inner_right_of_mem_orthogonal (hi v hv)
        (Submodule.sub_starProjection_mem_orthogonal (K := S) f)
    have hz : S.starProjection (B (f - S.starProjection f)) = 0 := by
      have h1 := Submodule.inner_right_of_mem_orthogonal
        (S.starProjection_apply_mem (B (f - S.starProjection f))) horth
      have h2 := Submodule.inner_right_of_mem_orthogonal
        (S.starProjection_apply_mem (B (f - S.starProjection f)))
        (Submodule.sub_starProjection_mem_orthogonal
          (K := S) (B (f - S.starProjection f)))
      rw [inner_sub_right, h1, real_inner_self_eq_norm_sq] at h2
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (S.starProjection (B (f - S.starProjection f)))]
    rw [map_sub, map_sub,
      Submodule.starProjection_eq_self_iff.mpr
        (hi _ (S.starProjection_apply_mem f))] at hz
    exact sub_eq_zero.mp hz

/-- Commutation at the single actual displacement is already the missing membership. -/
theorem displacement_eq_zero_iff_commutes_at_displacement :
    displacement = 0 ↔
      closure.starProjection (B displacement) = B (closure.starProjection displacement) := by
  rw [Submodule.starProjection_eq_self_iff.mpr displacement_mem,
    Submodule.starProjection_eq_self_iff]
  exact displacement_eq_zero_iff_reciprocal_mem

/-- Exact strong limit of the reciprocal projection defect. -/
theorem reciprocal_projection_defect_tendsto {G : ℕ → QHilbert}
    (h : Tendsto G atTop (𝓝 displacement)) :
    Tendsto (fun M => B (G M) - closure.starProjection (B (G M)))
      atTop (𝓝 (B displacement - closure.starProjection (B displacement))) :=
  (reciprocal_tendsto h).sub
    ((closure.starProjection.continuous.tendsto _).comp (reciprocal_tendsto h))

/-- The user's limit argument succeeds exactly when the extra projection defect vanishes. -/
theorem displacement_eq_zero_iff_defect_tendsto_zero {G : ℕ → QHilbert}
    (h : Tendsto G atTop (𝓝 displacement)) :
    displacement = 0 ↔
      Tendsto (fun M => B (G M) - closure.starProjection (B (G M)))
        atTop (𝓝 0) := by
  constructor
  · intro hd
    simpa only [hd, map_zero, sub_self] using reciprocal_projection_defect_tendsto h
  · intro hzero
    have he := tendsto_nhds_unique (reciprocal_projection_defect_tendsto h) hzero
    apply displacement_eq_zero_iff_reciprocal_mem.mpr
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm

/-- Residual orthogonality gives a quantitative lower obstruction to legal approximation. -/
theorem displacement_energy_le_reciprocal_error (v : QHilbert) (hv : v ∈ closure) :
    ‖toPareto displacement‖ ^ 2 ≤
      zetaTwo * ‖qResidual‖ * ‖B displacement - v‖ := by
  have hz := Submodule.inner_right_of_mem_orthogonal hv qResidual_mem_orthogonal
  have he : inner ℝ (B displacement - v) qResidual =
      inner ℝ displacement (B qResidual) := by
    rw [inner_sub_left, hz, sub_zero, B_symmetric]
  calc
    _ = zetaTwo * inner ℝ (B displacement - v) qResidual := by
      rw [he, displacement_p_energy]
    _ ≤ zetaTwo * (‖B displacement - v‖ * ‖qResidual‖) :=
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) zetaTwo_pos.le
    _ = _ := by ring

/-- Conditional RH reduction: commutation is not assumed elsewhere or established here. -/
theorem riemannHypothesis_of_reciprocal_commutes
    (h : ∀ f, closure.starProjection (B f) = B (closure.starProjection f)) :
    RiemannHypothesis :=
  riemannHypothesis_of_reciprocal_invariant
    ((reciprocal_commutes_iff_invariant closure).mp h)

/-- Conditional RH reduction retaining the additional zero-defect limit as a hypothesis. -/
theorem riemannHypothesis_of_reciprocal_defect_tendsto_zero
    {G : ℕ → QHilbert} (h : Tendsto G atTop (𝓝 displacement))
    (hz : Tendsto (fun M => B (G M) - closure.starProjection (B (G M)))
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_displacement_eq_zero
    ((displacement_eq_zero_iff_defect_tendsto_zero h).mpr hz)


/-- Iteration contracts every vector, including nonzero vectors. -/
theorem reciprocal_iterate_norm_le (f : QHilbert) (k : ℕ) :
    ‖((B : QHilbert → QHilbert)^[k]) f‖ ≤ (1 / 2 : ℝ)^k * ‖f‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ (1 / 2 : ℝ) * ‖((B : QHilbert → QHilbert)^[k]) f‖ := B_norm_le_half _
      _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ)^k * ‖f‖) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem reciprocal_iterate_tendsto_zero (f : QHilbert) :
    Tendsto (fun k : ℕ => ((B : QHilbert → QHilbert)^[k]) f) atTop (𝓝 0) := by
  apply squeeze_zero_norm (reciprocal_iterate_norm_le f)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖f‖

/-- Decay under iteration does not imply that the original vector or its image is zero. -/
theorem nonzero_reciprocal_with_decaying_iterates :
    ∃ f : QHilbert, f ≠ 0 ∧ B f ≠ 0 ∧
      Tendsto (fun k : ℕ => ((B : QHilbert → QHilbert)^[k]) f) atTop (𝓝 0) := by
  refine ⟨qOne, ?_, reciprocal_qOne_ne_zero, reciprocal_iterate_tendsto_zero qOne⟩
  intro h
  exact reciprocal_qOne_ne_zero (by simp [h])

/-- The extra quantity needed for the user's approximation argument. -/
theorem displacement_energy_le_approximation_error (g : QHilbert) :
    ‖toPareto displacement‖ ^ 2 ≤ zetaTwo * ‖qResidual‖ *
      (‖B g - closure.starProjection (B g)‖ + (1 / 2 : ℝ) * ‖g - displacement‖) := by
  have ht := norm_add_le (B displacement - B g) (B g - closure.starProjection (B g))
  rw [sub_add_sub_cancel] at ht
  rw [← map_sub] at ht
  have hb := B_norm_le_half (displacement - g)
  rw [norm_sub_rev displacement g] at hb
  have he : ‖B displacement - closure.starProjection (B g)‖ ≤
      ‖B g - closure.starProjection (B g)‖ + (1 / 2 : ℝ) * ‖g - displacement‖ := by
    linarith
  exact (displacement_energy_le_reciprocal_error _
    (closure.starProjection_apply_mem (B g))).trans
    (mul_le_mul_of_nonneg_left he (mul_nonneg zetaTwo_pos.le (norm_nonneg qResidual)))

end RiemannResearch.RH.QFullReciprocalLimits
