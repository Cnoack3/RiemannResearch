/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSimultaneousCRT
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import Mathlib.Tactic.Abel

/-!
# CRT representatives preserve the residualized carry Gram matrix

Source: user-provided Pareto First Projections and Transfer to Q Research Draft,
11 November 2026, Priority 1 and the invariant Schur complement section:
https://chatgpt.com/space/page_899f440a0304819182638fe62685b02e.
L can be the identity for Q or toParetoLinear for the same physical P vectors.
Only the synthesis changes; the same residue atom and projected subspace are used.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTRepresentativeInvariance
open ZetaTwoHilbert QSimultaneousCRT
open RiemannResearch.Analysis.ResidualizedProjectionKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (L : QHilbert →ₗ[ℝ] E) (W : Submodule ℝ E) [W.HasOrthogonalProjection]

/-- Literal complete residualized carry, in the chosen physical realization. -/
def carryResidual (m : ℕ) : E :=
  L (canonicalCarry m) - W.starProjection (L (canonicalCarry m))

theorem carryResidual_eq_neg_residue (m : ℕ) (hm : L (primeSynthesis m) ∈ W) :
    carryResidual L W m = -(L (qResidue m) - W.starProjection (L (qResidue m))) := by
  rw [carryResidual, canonicalCarry_eq, map_sub]
  exact residualized_representation W (L (primeSynthesis m)) (L (qResidue m)) hm

/-- Every alternative prime synthesis in W gives the same residualized carry. -/
theorem alternative_synthesis_residual (m : ℕ) (u : QHilbert)
    (hm : L (primeSynthesis m) ∈ W) (hu : L u ∈ W) :
    L (u - qResidue m) - W.starProjection (L (u - qResidue m)) =
      carryResidual L W m := by
  rw [map_sub, residualized_representation W (L u) (L (qResidue m)) hu,
    carryResidual_eq_neg_residue L W m hm]

/-- Complete Gram entry invariance; no infinite tail is removed. -/
theorem carry_gram_representative_invariant (m n : ℕ) (u v : QHilbert)
    (hm : L (primeSynthesis m) ∈ W) (hn : L (primeSynthesis n) ∈ W)
    (hu : L u ∈ W) (hv : L v ∈ W) :
    inner ℝ (L (u - qResidue m) - W.starProjection (L (u - qResidue m)))
      (L (v - qResidue n) - W.starProjection (L (v - qResidue n))) =
        inner ℝ (carryResidual L W m) (carryResidual L W n) := by
  rw [alternative_synthesis_residual L W m u hm hu,
    alternative_synthesis_residual L W n v hn hv]

/-- The target pairings, as well as the residualized Gram matrix, are invariant. -/
theorem carry_source_representative_invariant (m : ℕ) (u : QHilbert) (x : E)
    (hm : L (primeSynthesis m) ∈ W) (hu : L u ∈ W) :
    inner ℝ x (L (u - qResidue m) - W.starProjection (L (u - qResidue m))) =
      inner ℝ x (carryResidual L W m) := by
  rw [alternative_synthesis_residual L W m u hm hu]

end RiemannResearch.RH.QCRTRepresentativeInvariance
