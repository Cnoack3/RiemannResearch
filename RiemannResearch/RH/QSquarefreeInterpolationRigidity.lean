/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QMeasureInterpolation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import RiemannResearch.RH.QShiftedReciprocalBounds
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QFiniteSupportDualCriterion
import Mathlib.Tactic.Linarith

/-!
# Rigidity of squarefree projection displacements along measure interpolation

Source: the user's interpolation and tail-dichotomy argument, 28 October 2026.
The weight is `I - t B`. A displacement satisfying its exact normal equation
gives a squarefree annihilator with mean

  t * <r, B r> + ||d||^2 - t * <d, B d>.

The exact signed identity is retained before the lower estimate. For every
positive parameter at most one, physical boundedness of that displacement
forces the original squarefree residual to vanish. The actual boundedness
premise remains Open; a small interpolation parameter alone does not supply it.
The first lemmas consume a normal equation. The actual path below is constructed
by Banach's theorem, which discharges that equation. Its endpoints are zero
and the existing Q/Pareto displacement.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeInterpolationRigidity
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeResidualTail QFiniteSupportDualCriterion

def interpolationWitness (t : ℝ) (d : QHilbert) : QHilbert :=
  t • B (limitingResidual + d) - d

theorem interpolationWitness_mem_orthogonal (t : ℝ) (d : QHilbert)
    (hnormal : closure.starProjection (t • B (limitingResidual + d)) = d) :
    interpolationWitness t d ∈ closureᗮ := by
  simpa only [interpolationWitness, hnormal] using
    (Submodule.sub_starProjection_mem_orthogonal (K := closure)
      (t • B (limitingResidual + d)))

/-- Exact mean: all signed terms are retained. -/
theorem interpolationWitness_mean_energy (t : ℝ) (d : QHilbert)
    (hnormal : closure.starProjection (t • B (limitingResidual + d)) = d) :
    inner ℝ qOne (interpolationWitness t d) =
      t * inner ℝ limitingResidual (B limitingResidual) +
        ‖d‖ ^ 2 - t * inner ℝ d (B d) := by
  have hd : d ∈ closure := by
    rw [← hnormal]
    exact closure.starProjection_apply_mem _
  have hu := interpolationWitness_mem_orthogonal t d hnormal
  have hfp := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem qOne) hu
  have hrd : inner ℝ limitingResidual d = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hd
      limitingResidual_mem_squarefree_orthogonal
  have hcross := Submodule.inner_right_of_mem_orthogonal hd hu
  rw [interpolationWitness, inner_sub_right, inner_smul_right,
    map_add, inner_add_right, real_inner_self_eq_norm_sq] at hcross
  have hsym : inner ℝ limitingResidual (B d) =
      inner ℝ d (B limitingResidual) := by
    rw [← B_symmetric, real_inner_comm]
  calc
    inner ℝ qOne (interpolationWitness t d) =
        inner ℝ limitingResidual (interpolationWitness t d) := by
      change inner ℝ qOne (interpolationWitness t d) =
        inner ℝ (qOne - closure.starProjection qOne) (interpolationWitness t d)
      rw [inner_sub_left, hfp, sub_zero]
    _ = _ := by
      rw [interpolationWitness, inner_sub_right, inner_smul_right,
        map_add, inner_add_right, hrd, sub_zero, hsym]
      nlinarith

/-- Positivity of the interpolation supplies an actual coercive lower bound. -/
theorem interpolationWitness_mean_lower (t : ℝ) (ht : t ≤ 1) (d : QHilbert)
    (hnormal : closure.starProjection (t • B (limitingResidual + d)) = d) :
    t * inner ℝ limitingResidual (B limitingResidual) + (1 / 2 : ℝ) * ‖d‖ ^ 2 ≤
      inner ℝ qOne (interpolationWitness t d) := by
  rw [interpolationWitness_mean_energy t d hnormal]
  have hB := B_positive d
  have hhalf := twice_B_inner_le_norm_sq d
  have hprod := mul_nonneg (sub_nonneg.mpr ht) hB
  nlinarith

theorem residual_zero_of_interpolationWitness_mean_zero
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (d : QHilbert)
    (hnormal : closure.starProjection (t • B (limitingResidual + d)) = d)
    (hm : inner ℝ qOne (interpolationWitness t d) = 0) :
    limitingResidual = 0 := by
  have hlow := interpolationWitness_mean_lower t ht1 d hnormal
  rw [hm] at hlow
  have hB := B_positive limitingResidual
  have hzero : inner ℝ limitingResidual (B limitingResidual) = 0 := by
    nlinarith [sq_nonneg ‖d‖]
  exact B_faithful limitingResidual hzero

/-- Conditional research reduction. The physical bound remains Open. -/
theorem residual_zero_of_interpolation_displacement_bounded
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (d : QHilbert)
    (hnormal : closure.starProjection (t • B (limitingResidual + d)) = d)
    (C : ℝ) (hb : ∀ k : ℕ, |qSequence d k| ≤ C) :
    limitingResidual = 0 := by
  obtain ⟨D, hD⟩ := B_physical_bounded (limitingResidual + d)
  have hw : ∀ k : ℕ, |qSequence (interpolationWitness t d) k| ≤ t * D + C := by
    intro k
    have he : qSequence (interpolationWitness t d) k =
        t * qSequence (B (limitingResidual + d)) k - qSequence d k := by
      change qSequenceLinear (t • B (limitingResidual + d) - d) k = _
      rw [map_sub, map_smul]
      rfl
    rw [he]
    calc
      _ ≤ |t * qSequence (B (limitingResidual + d)) k| + |qSequence d k| :=
        by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le (t * qSequence (B (limitingResidual + d)) k) (-qSequence d k)
      _ = t * |qSequence (B (limitingResidual + d)) k| + |qSequence d k| := by
        rw [abs_mul, abs_of_pos ht]
      _ ≤ t * D + C := add_le_add
        (mul_le_mul_of_nonneg_left (hD k) ht.le) (hb k)
  have hC0 : 0 ≤ t * D + C := (abs_nonneg _).trans (hw 0)
  have hm := bounded_annihilator_mean_eq_zero (interpolationWitness t d)
    (interpolationWitness_mem_orthogonal t d hnormal) (t * D + C) hC0 hw
  exact residual_zero_of_interpolationWitness_mean_zero t ht ht1 d hnormal hm

/-- The actual squarefree projection displacement for the weight `I - t B`. -/
def pathDisplacement (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : QHilbert :=
  QMeasureInterpolation.displacement closure limitingResidual t ht0 ht1

theorem pathDisplacement_normal (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    closure.starProjection (t • B (limitingResidual + pathDisplacement t ht0 ht1)) =
      pathDisplacement t ht0 ht1 := by
  change closure.starProjection (t • B (limitingResidual +
    QMeasureInterpolation.displacement closure limitingResidual t ht0 ht1)) = _
  rw [map_smul]
  exact (QMeasureInterpolation.displacement_fixed_point
    closure limitingResidual t ht0 ht1).symm

theorem pathDisplacement_zero :
    pathDisplacement 0 (by norm_num) (by norm_num) = 0 := by
  exact QMeasureInterpolation.displacement_zero closure limitingResidual

theorem pathDisplacement_one :
    pathDisplacement 1 (by norm_num) (by norm_num) =
      QSquarefreeDisplacementRigidity.displacement := by
  have hd : QSquarefreeDisplacementRigidity.displacement =
      (1 : ℝ) • closure.starProjection (B (limitingResidual +
        QSquarefreeDisplacementRigidity.displacement)) := by
    rw [one_smul,
      ← QSquarefreeDisplacementRigidity.pResidual_eq_residual_add_displacement]
    exact QSquarefreeDisplacementResolvent.displacement_eq_projected_pResidual
  exact (QMeasureInterpolation.displacement_unique
    closure limitingResidual 1 (by norm_num) (by norm_num)
    QSquarefreeDisplacementRigidity.displacement hd).symm

theorem pathDisplacement_eq_zero_of_residual_eq_zero
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : limitingResidual = 0) :
    pathDisplacement t ht0 ht1 = 0 := by
  change QMeasureInterpolation.displacement closure limitingResidual t ht0 ht1 = 0
  symm
  apply QMeasureInterpolation.displacement_unique closure limitingResidual t ht0 ht1 0
  simp [hr]

/-- Every nontrivial interpolation step has exactly the same boundedness
obligation. The actual path normal equation has been discharged. -/
theorem path_bounded_iff_residual_zero (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (∃ C : ℝ, ∀ k : ℕ, |qSequence (pathDisplacement t ht.le ht1) k| ≤ C) ↔
      limitingResidual = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    exact residual_zero_of_interpolation_displacement_bounded t ht ht1
      (pathDisplacement t ht.le ht1) (pathDisplacement_normal t ht.le ht1) C hC
  · intro hr
    refine ⟨0, ?_⟩
    intro k
    rw [pathDisplacement_eq_zero_of_residual_eq_zero t ht.le ht1 hr]
    cases k <;> simp [qSequence]

theorem pathDisplacement_eq_zero_iff_residual_zero
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    pathDisplacement t ht.le ht1 = 0 ↔ limitingResidual = 0 := by
  constructor
  · intro hd
    apply (path_bounded_iff_residual_zero t ht ht1).mp
    refine ⟨0, ?_⟩
    intro k
    cases k <;> simp [hd, qSequence]
  · exact pathDisplacement_eq_zero_of_residual_eq_zero t ht.le ht1

/-- Hilbert-small positive interpolation steps can still have unbounded
physical coordinates: this is forced on the nonzero-residual branch. -/
theorem pathDisplacement_unbounded_of_residual_ne_zero
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hr : limitingResidual ≠ 0) (C : ℝ) :
    ∃ k : ℕ, C < |qSequence (pathDisplacement t ht.le ht1) k| := by
  by_contra h
  have hb : ∀ k : ℕ, |qSequence (pathDisplacement t ht.le ht1) k| ≤ C := by
    intro k
    exact le_of_not_gt (fun hk => h ⟨k, hk⟩)
  exact hr ((path_bounded_iff_residual_zero t ht ht1).mp ⟨C, hb⟩)

end RiemannResearch.RH.QSquarefreeInterpolationRigidity
