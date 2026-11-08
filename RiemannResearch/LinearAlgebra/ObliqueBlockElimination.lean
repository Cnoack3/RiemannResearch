/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel

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
end RiemannResearch.LinearAlgebra.ObliqueBlockElimination
