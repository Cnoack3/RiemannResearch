/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith

/-!
# Morse-index reduction

Adapted from the user-provided archive `combined_audited_lean_sources.zip`,
which describes these declarations as extracted from
`combined_audited_manuscript(4).pdf`. The manuscript itself was not bundled
with this continuation, so this module records archive provenance rather than
claiming page-level source verification.
-/


namespace RiemannResearch.RH.CombinedAudited

open Module

/-- If a functional is nonnegative on the kernel of a finite-dimensional
detector, every strictly negative subspace injects into the detector. -/
theorem negative_subspace_finrank_le_target
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (q : V → ℝ) (polar : V →ₗ[ℝ] W)
    (N : Submodule ℝ V)
    (hkernel : ∀ x, polar x = 0 → 0 ≤ q x)
    (hnegative : ∀ x, x ∈ N → x ≠ 0 → q x < 0) :
    finrank ℝ N ≤ finrank ℝ W := by
  let restricted : N →ₗ[ℝ] W := polar.comp N.subtype
  have hinj : Function.Injective restricted := by
    intro x y hxy
    have hpolar : polar ((x : V) - (y : V)) = 0 := by
      change restricted (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hnonneg : 0 ≤ q ((x : V) - (y : V)) :=
      hkernel ((x : V) - (y : V)) hpolar
    have hzero : (x : V) - (y : V) = 0 := by
      by_contra hne
      have hmem : (x : V) - (y : V) ∈ N := N.sub_mem x.property y.property
      have hneg : q ((x : V) - (y : V)) < 0 :=
        hnegative ((x : V) - (y : V)) hmem hne
      linarith
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- The user-provided two-polar-mode Morse reduction. Its decisive application
hypothesis is nonnegativity on the kernel of the actual polar map. -/
theorem negative_subspace_finrank_le_two
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (q : V → ℝ) (polar : V →ₗ[ℝ] (Fin 2 → ℝ))
    (N : Submodule ℝ V)
    (hkernel : ∀ x, polar x = 0 → 0 ≤ q x)
    (hnegative : ∀ x, x ∈ N → x ≠ 0 → q x < 0) :
    finrank ℝ N ≤ 2 := by
  simpa using negative_subspace_finrank_le_target q polar N hkernel hnegative

end RiemannResearch.RH.CombinedAudited
