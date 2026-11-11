/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Exact elimination for nonsymmetric block systems

Source: independently derived elementary block algebra for the user's
7 November 2026 canonical CRT update request. The RH consumer is the
screened difference-test system described in
`RH/CanonicalPrimePowerUpdatesResearch20261107.md`.

Physical orthogonal screening does not make a collocation matrix symmetric.
This theorem preserves both cross blocks and the signed Schur source.
-/

namespace RiemannResearch.LinearAlgebra.ObliqueBlockElimination
variable {R U W : Type*} [CommRing R] [AddCommGroup U] [AddCommGroup W]
  [Module R U] [Module R W]

/-- Exact elimination for a nonsymmetric block system.
No transpose relation or positivity of the Schur complement is assumed. -/
theorem block_elimination
    (A I : U →ₗ[R] U) (B : W →ₗ[R] U) (C : U →ₗ[R] W) (D : W →ₗ[R] W)
    (hIA : ∀ u, I (A u) = u) (x s : U) (y t : W)
    (h0 : A x + B y = s) (h1 : C x + D y = t) :
    x = I s - I (B y) ∧
      D y - C (I (B y)) = t - C (I s) := by
  have hx : x = I s - I (B y) := by
    calc
      x = I (A x) := (hIA x).symm
      _ = I (s - B y) := congrArg I (eq_sub_of_add_eq h0)
      _ = _ := map_sub I s (B y)
  refine ⟨hx, ?_⟩
  rw [hx, map_sub] at h1
  calc
    D y - C (I (B y)) =
        (C (I s) - C (I (B y)) + D y) - C (I s) := by abel
    _ = t - C (I s) := congrArg (fun z => z - C (I s)) h1

section Inverse
variable {K X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]
  [Module K X] [Module K Y] [FiniteDimensional K Y]

/-- The genuine Schur endomorphism of a nonsymmetric two-block system. -/
def schur (A : X ≃ₗ[K] X) (B : Y →ₗ[K] X) (C : X →ₗ[K] Y)
    (D : Y →ₗ[K] Y) : Y →ₗ[K] Y :=
  D - C.comp (A.symm.toLinearMap.comp B)

theorem schur_injective (A : X ≃ₗ[K] X) (B : Y →ₗ[K] X)
    (C : X →ₗ[K] Y) (D : Y →ₗ[K] Y)
    (hker : ∀ x y, A x + B y = 0 → C x + D y = 0 → y = 0) :
    Function.Injective (schur A B C D) := by
  intro y z hyz
  have hs : schur A B C D (y-z) = 0 := by rw [map_sub, hyz, sub_self]
  apply sub_eq_zero.mp
  apply hker (-(A.symm (B (y-z)))) (y-z)
  · simp
  · change D (y-z) - C (A.symm (B (y-z))) = 0 at hs
    rw [map_neg]
    simpa only [sub_eq_add_neg, add_comm] using hs

/-- Finite-dimensional Schur inversion follows from the full kernel test. -/
noncomputable def schurEquiv (A : X ≃ₗ[K] X) (B : Y →ₗ[K] X)
    (C : X →ₗ[K] Y) (D : Y →ₗ[K] Y)
    (hker : ∀ x y, A x + B y = 0 → C x + D y = 0 → y = 0) : Y ≃ₗ[K] Y :=
  LinearEquiv.ofInjectiveEndo (schur A B C D) (schur_injective A B C D hker)

theorem schur_solution (A : X ≃ₗ[K] X) (B : Y →ₗ[K] X)
    (C : X →ₗ[K] Y) (D : Y →ₗ[K] Y)
    (hker : ∀ x y, A x + B y = 0 → C x + D y = 0 → y = 0)
    (s : X) (t : Y) :
    let y := (schurEquiv A B C D hker).symm (t - C (A.symm s))
    let x := A.symm (s - B y)
    A x + B y = s ∧ C x + D y = t := by
  dsimp only
  constructor
  · simp
  · have h := (schurEquiv A B C D hker).apply_symm_apply (t-C (A.symm s))
    change D _ - C (A.symm (B _)) = t - C (A.symm s) at h
    rw [map_sub, map_sub]
    calc
      _ = (D _ - C (A.symm (B _))) + C (A.symm s) := by abel
      _ = _ := by rw [h]; abel

end Inverse

end RiemannResearch.LinearAlgebra.ObliqueBlockElimination
