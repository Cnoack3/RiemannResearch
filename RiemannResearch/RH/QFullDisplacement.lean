/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Matched projection displacement for every integer conductor

Source: Full_Conductor_RH_Projection_Machinery, 6 November 2026,
Section "The full-family displacement", task A1. The proof adapts the
generic change-of-metric algebra of QParetoClosedProjectionComparison.
The legal space below is literally the closure of all g_m, m >= 2.
No squarefree closure or analytic RH converse provider occurs in the types.
The witness identity retains both nonnegative energy terms. It does not
establish that either term vanishes.
-/

noncomputable section
open scoped Topology
namespace RiemannResearch.RH.QFullDisplacement
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QParetoClosedProjectionComparison QShiftedReciprocal
open QFullResidueProjection
open QReciprocalMetric

/-- Pareto closure of the very same all-conductor algebraic dictionary. -/
def paretoClosure : Submodule ℝ ThresholdHilbert :=
  (legalSpan.map paretoEquiv.toLinearMap).topologicalClosure

instance paretoClosure_hasOrthogonalProjection : paretoClosure.HasOrthogonalProjection := by
  unfold paretoClosure
  infer_instance

theorem toPareto_mem_iff (f : QHilbert) :
    toPareto f ∈ paretoClosure ↔ f ∈ closure :=
  mem_closure_map_iff legalSpan f

def qResidual : QHilbert := qOne - closure.starProjection qOne

def pResidual : QHilbert := qOne - pFit paretoClosure qOne

/-- Difference of the two projections onto the same full physical span. -/
def displacement : QHilbert :=
  closure.starProjection qOne - pFit paretoClosure qOne

theorem qResidual_mem_orthogonal : qResidual ∈ closureᗮ :=
  Submodule.sub_starProjection_mem_orthogonal qOne

theorem displacement_mem : displacement ∈ closure :=
  closure.sub_mem (closure.starProjection_apply_mem qOne)
    (pFit_mem closure paretoClosure toPareto_mem_iff qOne)

theorem pResidual_eq_residual_add_displacement :
    pResidual = qResidual + displacement := by
  unfold pResidual qResidual displacement
  abel

/-- The faithful change-of-metric witness. -/
def witness : QHilbert := B pResidual - displacement

theorem witness_mem_orthogonal : witness ∈ closureᗮ := by
  apply (closure.mem_orthogonal _).mpr
  intro v hv
  have hp : inner ℝ (toPareto v) (toPareto pResidual) = 0 := by
    unfold pResidual
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.inner_right_of_mem_orthogonal
      ((toPareto_mem_iff v).mpr hv)
      (Submodule.sub_starProjection_mem_orthogonal
        (K := paretoClosure) (toPareto qOne))
  rw [pareto_inner_identity] at hp
  have hp' : inner ℝ v pResidual - inner ℝ v (B pResidual) = 0 :=
    (mul_eq_zero.mp hp).resolve_left (ne_of_gt zetaTwo_pos)
  have hq := Submodule.inner_right_of_mem_orthogonal hv qResidual_mem_orthogonal
  rw [pResidual_eq_residual_add_displacement, inner_add_right, hq, zero_add] at hp'
  change inner ℝ v (B pResidual - displacement) = 0
  rw [inner_sub_right, pResidual_eq_residual_add_displacement]
  linarith

/-- Exact energy, retaining the residual correction and Pareto displacement. -/
theorem witness_mean_energy :
    zetaTwo * inner ℝ qOne witness =
      zetaTwo * inner ℝ qResidual (B qResidual) +
        ‖toPareto displacement‖ ^ 2 := by
  have hfw := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem qOne) witness_mem_orthogonal
  have hrd : inner ℝ qResidual displacement = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal displacement_mem qResidual_mem_orthogonal
  have hmean : inner ℝ qOne witness =
      inner ℝ qResidual (B qResidual) + inner ℝ qResidual (B displacement) := by
    calc
      _ = inner ℝ qResidual witness := by
        change inner ℝ qOne witness =
          inner ℝ (qOne - closure.starProjection qOne) witness
        rw [inner_sub_left, hfw, sub_zero]
      _ = _ := by
        rw [witness, inner_sub_right, hrd, sub_zero,
          pResidual_eq_residual_add_displacement, map_add, inner_add_right]
  have hcross := Submodule.inner_right_of_mem_orthogonal
    displacement_mem witness_mem_orthogonal
  rw [witness, inner_sub_right, pResidual_eq_residual_add_displacement,
    map_add, inner_add_right, real_inner_self_eq_norm_sq] at hcross
  have hsym : inner ℝ qResidual (B displacement) =
      inner ℝ displacement (B qResidual) := by
    rw [← B_symmetric, real_inner_comm]
  have hmetric := pareto_inner_identity displacement displacement
  simp only [real_inner_self_eq_norm_sq] at hmetric
  have hc : inner ℝ displacement (B qResidual) =
      ‖displacement‖ ^ 2 - inner ℝ displacement (B displacement) := by linarith
  rw [hmean, hsym, hc, hmetric]
  ring

theorem qResidual_eq_zero_of_witness_mean_zero (hm : inner ℝ qOne witness = 0) :
    qResidual = 0 := by
  have he := witness_mean_energy
  rw [hm, mul_zero] at he
  have hp := B_positive qResidual
  have hz : zetaTwo * inner ℝ qResidual (B qResidual) = 0 := by
    nlinarith [mul_nonneg zetaTwo_pos.le hp, sq_nonneg ‖toPareto displacement‖]
  exact B_faithful qResidual
    ((mul_eq_zero.mp hz).resolve_left (ne_of_gt zetaTwo_pos))

/-- Zero residual means the target actually lies in the full legal closure. -/
theorem qResidual_eq_zero_iff : qResidual = 0 ↔ qOne ∈ closure := by
  unfold qResidual
  rw [sub_eq_zero]
  constructor
  · intro h
    exact Submodule.starProjection_eq_self_iff.mp h.symm
  · intro h
    exact (Submodule.starProjection_eq_self_iff.mpr h).symm

theorem displacement_eq_zero_of_qResidual_eq_zero (hr : qResidual = 0) :
    displacement = 0 := by
  have hq : closure.starProjection qOne = qOne :=
    Submodule.starProjection_eq_self_iff.mpr (qResidual_eq_zero_iff.mp hr)
  have hp : pFit paretoClosure qOne = qOne := by
    apply paretoEquiv.injective
    change toPareto (pFit paretoClosure qOne) = toPareto qOne
    rw [toPareto_pFit]
    exact Submodule.starProjection_eq_self_iff.mpr
      ((toPareto_mem_iff qOne).mpr (qResidual_eq_zero_iff.mp hr))
  simp [displacement, hq, hp]

/-- The full-space displacement is the projected smoothed Pareto residual. -/
theorem displacement_eq_projected_pResidual :
    displacement = closure.starProjection (B pResidual) := by
  have hzero : closure.starProjection witness = 0 := by
    have h1 := Submodule.inner_right_of_mem_orthogonal
      (closure.starProjection_apply_mem witness) witness_mem_orthogonal
    have h2 := Submodule.inner_right_of_mem_orthogonal
      (closure.starProjection_apply_mem witness)
      (Submodule.sub_starProjection_mem_orthogonal (K := closure) witness)
    rw [inner_sub_right, h1, real_inner_self_eq_norm_sq] at h2
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (closure.starProjection witness)]
  have heq : closure.starProjection (B pResidual) = displacement := by
    rw [witness, map_sub,
      Submodule.starProjection_eq_self_iff.mpr displacement_mem] at hzero
    exact sub_eq_zero.mp hzero
  exact heq.symm

/-- Exact full-family response, without a boundedness or tail premise. -/
theorem displacement_fixed_point :
    displacement = closure.starProjection (B qResidual) +
      closure.starProjection (B displacement) := by
  calc
    displacement = closure.starProjection (B pResidual) :=
      displacement_eq_projected_pResidual
    _ = closure.starProjection (B (qResidual + displacement)) := by
      rw [← pResidual_eq_residual_add_displacement]
    _ = _ := by rw [map_add, map_add]

/-- The reversed metric expansion reproduces the full Pareto normal equation. -/
theorem displacement_swapped_normal_equation (v : QHilbert) (hv : v ∈ closure) :
    inner ℝ (toPareto (D qResidual)) (toPareto v) =
      inner ℝ (toPareto displacement) (toPareto v) := by
  have hc := Submodule.inner_right_of_mem_orthogonal hv witness_mem_orthogonal
  rw [witness, inner_sub_right, pResidual_eq_residual_add_displacement,
    map_add, inner_add_right] at hc
  rw [pareto_inner_D, pareto_inner_identity]
  have h1 : inner ℝ (B qResidual) v = inner ℝ v (B qResidual) :=
    real_inner_comm _ _
  have h2 : inner ℝ displacement v = inner ℝ v displacement :=
    real_inner_comm _ _
  have h3 : inner ℝ displacement (B v) = inner ℝ v (B displacement) := by
    rw [← B_symmetric, real_inner_comm]
  rw [h1, h2, h3]
  congr 1
  linarith

/-- The cross term is exactly the Pareto displacement energy, not an extra zero. -/
theorem displacement_p_energy :
    ‖toPareto displacement‖ ^ 2 =
      zetaTwo * inner ℝ displacement (B qResidual) := by
  have h := displacement_swapped_normal_equation displacement displacement_mem
  rw [pareto_inner_D, real_inner_self_eq_norm_sq] at h
  rw [real_inner_comm displacement (B qResidual)] at h
  exact h.symm

/-- Conditional reduction: the projected reciprocal residual must still be shown zero. -/
theorem displacement_eq_zero_iff_projected_residual_eq_zero :
    displacement = 0 ↔ closure.starProjection (B qResidual) = 0 := by
  constructor
  · intro hd
    have h := displacement_fixed_point
    simpa only [hd, map_zero, add_zero] using h.symm
  · intro h
    have hz := Submodule.inner_right_of_mem_orthogonal displacement_mem
      (Submodule.sub_starProjection_mem_orthogonal (K := closure) (B qResidual))
    rw [h, sub_zero] at hz
    have he := displacement_p_energy
    rw [hz, mul_zero] at he
    have hle := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq displacement
    by_contra hd
    have hp : 0 < zetaTwo * ‖displacement‖ ^ 2 :=
      mul_pos zetaTwo_pos (sq_pos_of_pos (norm_pos_iff.mpr hd))
    nlinarith

end RiemannResearch.RH.QFullDisplacement
