/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform evaluation on a complete subspace of bounded physical Q sequences

Source: the bounded-space step of `SingleConductorProjectionBound.md`.
The use of the uniform boundedness principle improves this step from finite
dimensional subspaces to arbitrary complete subspaces of bounded sequences.
The Banach--Steinhaus theorem is supplied by Mathlib; no arithmetic bound on
the canonical growing legal spaces is inferred.
-/

noncomputable section
namespace RiemannResearch.RH.QBoundedSubspaceEvaluation
open ZetaTwoHilbert ZetaTwoProbability
open scoped BigOperators

/-- Pointwise bounded physical sequences in a complete subspace have one
evaluation constant controlled by the Hilbert norm. -/
theorem exists_uniform_physical_bound
    (U : Submodule ℝ QHilbert) [CompleteSpace U]
    (hbounded : ∀ u : QHilbert, u ∈ U → ∃ C : ℝ,
      ∀ n : ℕ, |qSequence u n| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖ := by
  let T : ℕ → U →L[ℝ] ℝ := fun n => (qEvalCLM n).comp U.subtypeL
  have hpoint : ∀ u : U, ∃ C : ℝ, ∀ n : ℕ, ‖T n u‖ ≤ C := by
    intro u
    obtain ⟨C, hC⟩ := hbounded u u.property
    refine ⟨C, ?_⟩
    intro n
    simpa only [T, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, qEvalCLM_apply, Real.norm_eq_abs] using hC n
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro u hu n
  calc
    |qSequence u n| = ‖T n ⟨u, hu⟩‖ := by
      simp only [T, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply, qEvalCLM_apply, Real.norm_eq_abs]
    _ ≤ ‖T n‖ * ‖u‖ := (T n).le_opNorm ⟨u, hu⟩
    _ ≤ max C 0 * ‖u‖ := mul_le_mul_of_nonneg_right
      ((hC n).trans (le_max_left C 0)) (norm_nonneg u)

/-- The same constant bounds every physical evaluation after orthogonal
projection onto the fixed complete bounded-function subspace. -/
theorem exists_uniform_projection_physical_bound
    (U : Submodule ℝ QHilbert) [CompleteSpace U] [U.HasOrthogonalProjection]
    (hbounded : ∀ u : QHilbert, u ∈ U → ∃ C : ℝ,
      ∀ n : ℕ, |qSequence u n| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : QHilbert,
      ∀ n : ℕ, |qSequence (U.starProjection f) n| ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_physical_bound U hbounded
  refine ⟨C, hC, ?_⟩
  intro f n
  have hproj : ‖U.starProjection f‖ ≤ ‖f‖ := by
    calc
      _ ≤ ‖U.starProjection‖ * ‖f‖ := U.starProjection.le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le U) (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  exact (hbound (U.starProjection f) (U.starProjection_apply_mem f) n).trans
    (mul_le_mul_of_nonneg_left hproj hC)

/-- A bounded physical sequence pairs continuously with the complete Q-L1
norm, with its literal physical supremum constant. -/
theorem inner_le_physical_bound_mul_qL1 (u f : QHilbert) (M : ℝ)
    (hu : ∀ n : ℕ, |qSequence u n| ≤ M) :
    inner ℝ u f ≤ M * qL1 f := by
  have hpoint (n : ℕ) :
      positiveQWeight n * qSequence u n * qSequence f n ≤
        M * (positiveQWeight n * |qSequence f n|) := by
    calc
      _ ≤ |positiveQWeight n * qSequence u n * qSequence f n| := le_abs_self _
      _ = positiveQWeight n * |qSequence u n| * |qSequence f n| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n)]
      _ ≤ positiveQWeight n * M * |qSequence f n| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hu n) (positiveQWeight_nonneg n))
          (abs_nonneg _)
      _ = _ := by ring
  rw [qInner_weighted]
  have hs := (qSequence_product_summable u f).tsum_le_tsum hpoint
    ((qL1_summable f).mul_left M)
  simpa only [tsum_mul_left, qL1] using hs

/-- Uniform evaluation on U upgrades the projection from an L2 contraction
to an L1-to-L2 bound. This avoids choosing an orthonormal basis. -/
theorem abs_inner_le_physical_bound_mul_qL1 (u f : QHilbert) (M : ℝ)
    (hu : ∀ n : ℕ, |qSequence u n| ≤ M) :
    |inner ℝ u f| ≤ M * qL1 f := by
  have hneg : ∀ n : ℕ, |qSequence (-u) n| ≤ M := by
    intro n
    change |qSequenceLinear (-u) n| ≤ M
    rw [map_neg]
    change |-qSequence u n| ≤ M
    rw [abs_neg]
    exact hu n
  have hlo := inner_le_physical_bound_mul_qL1 (-u) f M hneg
  rw [inner_neg_left] at hlo
  exact abs_le.mpr ⟨by linarith, inner_le_physical_bound_mul_qL1 u f M hu⟩

/-- Uniform evaluation on U upgrades the projection from an L2 contraction
to an L1-to-L2 bound. This avoids choosing an orthonormal basis. -/
theorem projection_norm_le_qL1
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖) (f : QHilbert) :
    ‖U.starProjection f‖ ≤ C * qL1 f := by
  have hself : inner ℝ (U.starProjection f) f = ‖U.starProjection f‖ ^ 2 := by
    have horth := U.starProjection_inner_eq_zero f (U.starProjection f)
      (U.starProjection_apply_mem f)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at horth
    rw [real_inner_comm]
    linarith
  have h := inner_le_physical_bound_mul_qL1 (U.starProjection f) f
    (C * ‖U.starProjection f‖)
    (hbound (U.starProjection f) (U.starProjection_apply_mem f))
  rw [hself] at h
  have hnonneg : 0 ≤ C * qL1 f := mul_nonneg hC (qL1_nonneg f)
  by_cases hz : ‖U.starProjection f‖ = 0
  · simpa only [hz] using hnonneg
  · have hpos : 0 < ‖U.starProjection f‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      ‖U.starProjection f‖ * ‖U.starProjection f‖ =
          ‖U.starProjection f‖ ^ 2 := by ring
      _ ≤ (C * ‖U.starProjection f‖) * qL1 f := h
      _ = (C * qL1 f) * ‖U.starProjection f‖ := by ring

/-- The physical projection itself is bounded by C squared times the Q-L1
norm of its input. Applied to a nonnegative residue atom, this is a mean bound. -/
theorem projection_physical_le_qL1
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖) (f : QHilbert) (n : ℕ) :
    |qSequence (U.starProjection f) n| ≤ C ^ 2 * qL1 f := by
  calc
    _ ≤ C * ‖U.starProjection f‖ :=
      hbound (U.starProjection f) (U.starProjection_apply_mem f) n
    _ ≤ C * (C * qL1 f) := mul_le_mul_of_nonneg_left
      (projection_norm_le_qL1 U C hC hbound f) hC
    _ = _ := by ring

end RiemannResearch.RH.QBoundedSubspaceEvaluation
