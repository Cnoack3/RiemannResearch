/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Linear maps on submodule quotients

This module records generic identities for linear maps induced on quotient
modules.
-/

universe u v w

namespace RiemannResearch.LinearAlgebra

/-- If two linear maps preserve the relevant submodules and their composite
differs from multiplication by `n` by an element of the source submodule,
then the induced composite on quotient modules is multiplication by `n`. -/
theorem mapQ_comp_eq_nsmul_id
    {k : Type u} {M : Type v} {N : Type w} [CommRing k]
    [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    (p : Submodule k M) (q : Submodule k N)
    (f : M →ₗ[k] N) (g : N →ₗ[k] M)
    (hf : p ≤ Submodule.comap f q)
    (hg : q ≤ Submodule.comap g p)
    (n : ℕ)
    (hcomp : ∀ x : M, g (f x) - n • x ∈ p) :
    (q.mapQ p g hg).comp (p.mapQ q f hf) =
      n • LinearMap.id := by
  ext x
  simp only [LinearMap.comp_apply]
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mapQ_apply]
  change Submodule.Quotient.mk (g (f x)) =
    Submodule.Quotient.mk (n • x)
  exact (Submodule.Quotient.eq p).2 (hcomp x)

end RiemannResearch.LinearAlgebra
