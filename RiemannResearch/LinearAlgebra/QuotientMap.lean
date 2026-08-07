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

universe u v w x

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

/-- Descend a bilinear map through quotient modules when each relation
submodule is sent into the target relation submodule in both variables. -/
def bilinearMapQ
    {k : Type u} {M : Type v} {N : Type w} {P : Type x} [CommRing k]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module k M] [Module k N] [Module k P]
    (p : Submodule k M) (q : Submodule k N) (r : Submodule k P)
    (b : M →ₗ[k] N →ₗ[k] P)
    (hp : ∀ m ∈ p, ∀ n, b m n ∈ r)
    (hq : ∀ m n, n ∈ q → b m n ∈ r) :
    M ⧸ p →ₗ[k] (N ⧸ q →ₗ[k] P ⧸ r) := by
  let bRight : M →ₗ[k] (N ⧸ q →ₗ[k] P ⧸ r) :=
    { toFun := fun m => q.mapQ r (b m) (by
        intro n hn
        exact hq m n hn)
      map_add' := by
        intro m₁ m₂
        apply q.linearMap_qext
        ext n
        change (Submodule.Quotient.mk (b (m₁ + m₂) n) : P ⧸ r) =
          Submodule.Quotient.mk (b m₁ n) + Submodule.Quotient.mk (b m₂ n)
        simp
      map_smul' := by
        intro a m
        apply q.linearMap_qext
        ext n
        change (Submodule.Quotient.mk (b (a • m) n) : P ⧸ r) =
          Submodule.Quotient.mk (a • b m n)
        simp }
  exact p.liftQ bRight (by
    intro m hm
    rw [LinearMap.mem_ker]
    apply q.linearMap_qext
    ext n
    change (Submodule.Quotient.mk (b m n) : P ⧸ r) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hp m hm n)

@[simp]
theorem bilinearMapQ_mk_mk
    {k : Type u} {M : Type v} {N : Type w} {P : Type x} [CommRing k]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module k M] [Module k N] [Module k P]
    (p : Submodule k M) (q : Submodule k N) (r : Submodule k P)
    (b : M →ₗ[k] N →ₗ[k] P)
    (hp : ∀ m ∈ p, ∀ n, b m n ∈ r)
    (hq : ∀ m n, n ∈ q → b m n ∈ r)
    (m : M) (n : N) :
    bilinearMapQ p q r b hp hq (Submodule.Quotient.mk m)
        (Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (b m n) := by
  simp [bilinearMapQ]

/-- Associativity of a bilinear operation descends to the quotient. -/
theorem bilinearMapQ_assoc
    {k : Type u} {M : Type v} [CommRing k]
    [AddCommGroup M] [Module k M]
    (p : Submodule k M)
    (b : M →ₗ[k] M →ₗ[k] M)
    (hp : ∀ m ∈ p, ∀ n, b m n ∈ p)
    (hq : ∀ m n, n ∈ p → b m n ∈ p)
    (hassoc : ∀ m n t, b (b m n) t = b m (b n t))
    (m n t : M ⧸ p) :
    bilinearMapQ p p p b hp hq (bilinearMapQ p p p b hp hq m n) t =
      bilinearMapQ p p p b hp hq m (bilinearMapQ p p p b hp hq n t) := by
  refine Submodule.Quotient.induction_on p m ?_
  intro m
  refine Submodule.Quotient.induction_on p n ?_
  intro n
  refine Submodule.Quotient.induction_on p t ?_
  intro t
  simp [hassoc]

/-- A left identity for a bilinear operation remains a left identity after
passing to the quotient. -/
theorem bilinearMapQ_left_identity
    {k : Type u} {M : Type v} [CommRing k]
    [AddCommGroup M] [Module k M]
    (p : Submodule k M)
    (b : M →ₗ[k] M →ₗ[k] M)
    (hp : ∀ m ∈ p, ∀ n, b m n ∈ p)
    (hq : ∀ m n, n ∈ p → b m n ∈ p)
    (e : M) (he : ∀ m, b e m = m)
    (m : M ⧸ p) :
    bilinearMapQ p p p b hp hq (Submodule.Quotient.mk e) m = m := by
  refine Submodule.Quotient.induction_on p m ?_
  intro m
  simp [he]

/-- A right identity for a bilinear operation remains a right identity after
passing to the quotient. -/
theorem bilinearMapQ_right_identity
    {k : Type u} {M : Type v} [CommRing k]
    [AddCommGroup M] [Module k M]
    (p : Submodule k M)
    (b : M →ₗ[k] M →ₗ[k] M)
    (hp : ∀ m ∈ p, ∀ n, b m n ∈ p)
    (hq : ∀ m n, n ∈ p → b m n ∈ p)
    (e : M) (he : ∀ m, b m e = m)
    (m : M ⧸ p) :
    bilinearMapQ p p p b hp hq m (Submodule.Quotient.mk e) = m := by
  refine Submodule.Quotient.induction_on p m ?_
  intro m
  simp [he]

end RiemannResearch.LinearAlgebra
