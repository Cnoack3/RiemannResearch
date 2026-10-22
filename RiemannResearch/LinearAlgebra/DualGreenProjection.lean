/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Abstract dual Green projection

This module formalizes the right-inverse and weighted Pythagorean argument
underlying Theorem 2.1 of the user-supplied report
`rh_irreducible_targets_progress_2026-09-03.pdf`. The report supports the
proof strategy and terminology. The abstract declarations below do not by
themselves establish the report's finite prime-curvature kernel or positivity
claims; those require concrete providers for `D`, `R`, `S`, `B`, and `C`.
-/

namespace RiemannResearch.LinearAlgebra

variable {V U : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup U] [Module ℝ U]

abbrev RealBilin (M : Type*) [AddCommGroup M] [Module ℝ M] :=
  LinearMap.BilinForm ℝ M

def greenOperator (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) : U →ₗ[ℝ] U :=
  D.comp R

def dualGreenProjection
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U) : V →ₗ[ℝ] V :=
  R.comp (S.comp D)

@[simp] theorem dualGreenProjection_apply
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U) (z : V) :
    dualGreenProjection D R S z = R (S (D z)) := rfl

theorem dualGreenProjection_mapsTo
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U)
    (hG : Function.RightInverse S (greenOperator D R))
    (z : V) :
    D (dualGreenProjection D R S z) = D z := by
  exact hG (D z)

theorem dualGreenProjection_residual_mem_ker
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U)
    (hG : Function.RightInverse S (greenOperator D R))
    (z : V) :
    z - dualGreenProjection D R S z ∈ LinearMap.ker D := by
  change D (z - dualGreenProjection D R S z) = 0
  rw [D.map_sub, dualGreenProjection_mapsTo D R S hG z, sub_self]

theorem dualGreenProjection_idempotent
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U)
    (hG : Function.RightInverse S (greenOperator D R)) :
    (dualGreenProjection D R S).comp (dualGreenProjection D R S) =
      dualGreenProjection D R S := by
  apply LinearMap.ext
  intro z
  change R (S (D (R (S (D z))))) = R (S (D z))
  have hz := hG (D z)
  change D (R (S (D z))) = D z at hz
  rw [hz]

theorem dualGreenProjection_factorization
    (B : RealBilin V) (C : RealBilin U)
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U)
    (hdual : ∀ (lam : U) (v : V), B (R lam) v = C lam (D v))
    (z v : V) :
    B (dualGreenProjection D R S z) v = C (S (D z)) (D v) := by
  exact hdual (S (D z)) v

theorem dualGreenProjection_orthogonal_ker
    (B : RealBilin V) (C : RealBilin U)
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U)
    (hdual : ∀ (lam : U) (v : V), B (R lam) v = C lam (D v))
    (z k : V) (hk : k ∈ LinearMap.ker D) :
    B (dualGreenProjection D R S z) k = 0 := by
  rw [dualGreenProjection_factorization B C D R S hdual, show D k = 0 from hk]
  exact map_zero (C (S (D z)))

theorem dualGreen_energy
    (B : RealBilin V) (C : RealBilin U)
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U)
    (hG : Function.RightInverse S (greenOperator D R))
    (hdual : ∀ (lam : U) (v : V), B (R lam) v = C lam (D v))
    (z : V) :
    B (dualGreenProjection D R S z) (dualGreenProjection D R S z) =
      C (S (D z)) (D z) := by
  rw [dualGreenProjection_factorization B C D R S hdual]
  rw [dualGreenProjection_mapsTo D R S hG]

theorem dualGreen_pythagoras
    (B : RealBilin V) (C : RealBilin U)
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U)
    (hG : Function.RightInverse S (greenOperator D R))
    (hdual : ∀ (lam : U) (v : V), B (R lam) v = C lam (D v))
    (hBsymm : ∀ v w : V, B v w = B w v)
    {z x : V} (hx : D x = D z) :
    B x x =
      C (S (D z)) (D z) +
        B (x - dualGreenProjection D R S z)
          (x - dualGreenProjection D R S z) := by
  let q := dualGreenProjection D R S z
  have hDq : D q = D z := dualGreenProjection_mapsTo D R S hG z
  have hker : D (x - q) = 0 := by
    rw [D.map_sub, hx, hDq, sub_self]
  have hcross : B q (x - q) = 0 := by
    change B (R (S (D z))) (x - q) = 0
    rw [hdual, hker]
    exact map_zero (C (S (D z)))
  have hcross' : B (x - q) q = 0 := by
    rw [hBsymm, hcross]
  have hq : B q q = C (S (D z)) (D z) :=
    dualGreen_energy B C D R S hG hdual z
  calc
    B x x = B (q + (x - q)) (q + (x - q)) := by
      congr 2 <;> abel
    _ = B q q + B q (x - q) + B (x - q) q +
          B (x - q) (x - q) := by
      simp only [map_add, LinearMap.add_apply]
      ring
    _ = C (S (D z)) (D z) +
          B (x - q) (x - q) := by rw [hcross, hcross', hq]; ring

theorem dualGreen_minimizes
    (B : RealBilin V) (C : RealBilin U)
    (D : V →ₗ[ℝ] U) (R : U →ₗ[ℝ] V) (S : U →ₗ[ℝ] U)
    (hG : Function.RightInverse S (greenOperator D R))
    (hdual : ∀ (lam : U) (v : V), B (R lam) v = C lam (D v))
    (hBsymm : ∀ v w : V, B v w = B w v)
    (hBnonneg : ∀ v : V, 0 ≤ B v v)
    {z x : V} (hx : D x = D z) :
    C (S (D z)) (D z) ≤ B x x := by
  rw [dualGreen_pythagoras B C D R S hG hdual hBsymm hx]
  exact le_add_of_nonneg_right (hBnonneg _)

end RiemannResearch.LinearAlgebra
