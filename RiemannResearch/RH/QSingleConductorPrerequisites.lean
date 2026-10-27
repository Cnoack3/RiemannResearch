/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.QBoundedSubspaceEvaluation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QConductorDecay
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-subspace prerequisites for the single-conductor response estimate

Source: user-provided argument in `SingleConductorProjectionBound.md`;
the boundedness and natural-scale projection-loss steps are assembled here.

Bounded physical sequences are preserved by adjoining one residue atom.
The resulting evaluation bounds can be chosen uniformly on any finite set
of conductors. For large conductors, projection loss is smaller than one
quarter of the natural squared-norm scale.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSingleConductorPrerequisites
open ZetaTwoHilbert ZetaTwoProbability QBoundedSubspaceEvaluation

/-- Adjoining any one residue atom preserves bounded physical sequences. -/
theorem sup_residue_physical_bounded
    (U : Submodule ℝ QHilbert)
    (hbounded : ∀ u : QHilbert, u ∈ U →
      ∃ C : ℝ, ∀ n : ℕ, |qSequence u n| ≤ C)
    (d : ℕ) (w : QHilbert)
    (hw : w ∈ U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)) :
    ∃ C : ℝ, ∀ n : ℕ, |qSequence w n| ≤ C := by
  rcases Submodule.mem_sup.mp hw with ⟨u, hu, v, hv, rfl⟩
  rcases Submodule.mem_span_singleton.mp hv with ⟨a, rfl⟩
  obtain ⟨C, hC⟩ := hbounded u hu
  refine ⟨C + |a|, ?_⟩
  intro n
  change |qSequenceLinear (u + a • qResidue d) n| ≤ C + |a|
  rw [map_add, map_smul]
  change |qSequence u n + a * qSequence (qResidue d) n| ≤ C + |a|
  calc
    _ ≤ |qSequence u n| + |a * qSequence (qResidue d) n| := abs_add_le _ _
    _ = |qSequence u n| + |a| * |qSequence (qResidue d) n| := by rw [abs_mul]
    _ ≤ C + |a| * 1 := add_le_add (hC n)
      (mul_le_mul_of_nonneg_left (qResidue_physical_abs_le_one d n) (abs_nonneg a))
    _ = _ := by ring

/-- The finitely many small-conductor spaces have a common projection bound. -/
theorem exists_finite_conductor_projection_physical_bound
    (U : Submodule ℝ QHilbert) [FiniteDimensional ℝ U]
    (hbounded : ∀ u : QHilbert, u ∈ U →
      ∃ C : ℝ, ∀ n : ℕ, |qSequence u n| ≤ C)
    (D : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, d < D → ∀ f : QHilbert, ∀ n : ℕ,
      |qSequence ((U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)).starProjection f) n| ≤
        C * ‖f‖ := by
  have hfamily : ∀ i : Fin D, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : QHilbert, ∀ n : ℕ,
      |qSequence ((U ⊔ Submodule.span ℝ ({qResidue i.val} : Set QHilbert)).starProjection f) n| ≤
        C * ‖f‖ := by
    intro i
    exact exists_uniform_projection_physical_bound
      (U ⊔ Submodule.span ℝ ({qResidue i.val} : Set QHilbert))
      (sup_residue_physical_bounded U hbounded i.val)
  choose c hc hb using hfamily
  refine ⟨∑ i : Fin D, c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro d hd f n
  have hle : c ⟨d, hd⟩ ≤ ∑ i : Fin D, c i :=
    Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ (⟨d, hd⟩ : Fin D))
  exact (hb ⟨d, hd⟩ f n).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg f))

/-- For every fixed bounded physical space, a sufficiently large residue atom
retains at least one quarter of its reciprocal-conductor squared-norm scale. -/
theorem eventually_residue_residual_norm_sq_lower
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖) :
    ∀ᶠ d : ℕ in atTop, 2 ≤ d ∧
      1 / (4 * zetaTwo * d) ≤
        ‖qResidue d - U.starProjection (qResidue d)‖ ^ 2 := by
  have hzeta := zetaTwo_pos
  have ht := mul_qResidue_projection_norm_sq_tendsto_zero U C hC hbound
  have hsmall : ∀ᶠ d : ℕ in atTop,
      (d : ℝ) * ‖U.starProjection (qResidue d)‖ ^ 2 < 1 / (4 * zetaTwo) :=
    (tendsto_order.1 ht).2 _ (by positivity)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmall] with d hd hs
  refine ⟨hd, ?_⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hproj : ‖U.starProjection (qResidue d)‖ ^ 2 ≤
      (1 / (4 * zetaTwo)) / (d : ℝ) :=
    (le_div_iff₀ hdpos).mpr (by nlinarith [hs.le])
  rw [div_div] at hproj
  have hnorm := qResidue_norm_sq_ge_half_div d hd
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection (qResidue d) U
  simp only [Submodule.starProjection_orthogonal_val] at hpyth
  have hdouble : 1 / (2 * zetaTwo * d) = 2 * (1 / (4 * zetaTwo * d)) := by
    field_simp [hdpos.ne', zetaTwo_pos.ne']
    <;> ring
  rw [hdouble] at hnorm
  nlinarith

/-- Threshold form used when joining the finite and large-conductor estimates. -/
theorem exists_residue_residual_norm_sq_lower_threshold
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 2 ≤ d ∧
      1 / (4 * zetaTwo * d) ≤
        ‖qResidue d - U.starProjection (qResidue d)‖ ^ 2 :=
  eventually_atTop.1 (eventually_residue_residual_norm_sq_lower U C hC hbound)

end RiemannResearch.RH.QSingleConductorPrerequisites
