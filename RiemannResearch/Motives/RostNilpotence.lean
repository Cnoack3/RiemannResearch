/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.Idempotents

/-!
# Abstract Rost nilpotence and projector lifting

This module formalizes the ring-theoretic and categorical consequences of Rost
nilpotence. It does not construct Chow groups, correspondences, Chow motives,
or prove geometric Rost nilpotence. Once base change is available as an
additive functor on motives, this is the target API for lifting projectors.

The interface follows Chernousov--Gille--Merkurjev, *Motivic decomposition of
isotropic projective homogeneous varieties*, Theorem 8.2, and Brosnan,
*A short proof of Rost nilpotence via refined correspondences*.
-/

namespace RiemannResearch.Motives

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

section Rings

variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

/-- Every element in the kernel of a ring homomorphism is nilpotent. -/
def IsRostNilpotent (f : R →+* S) : Prop :=
  ∀ x, f x = 0 → IsNilpotent x

/-- The kernel is killed elementwise by one explicit power. -/
def HasKernelExponent (f : R →+* S) (n : ℕ) : Prop :=
  ∀ x, f x = 0 → x ^ n = 0

theorem isRostNilpotent_iff (f : R →+* S) :
    IsRostNilpotent f ↔ ∀ x ∈ RingHom.ker f, IsNilpotent x := by
  constructor
  · intro h x hx
    exact h x (RingHom.mem_ker.mp hx)
  · intro h x hx
    exact h x (RingHom.mem_ker.mpr hx)

theorem HasKernelExponent.isRostNilpotent {f : R →+* S} {n : ℕ}
    (h : HasKernelExponent f n) : IsRostNilpotent f := by
  intro x hx
  exact ⟨n, h x hx⟩

theorem isRostNilpotent_id : IsRostNilpotent (RingHom.id R) := by
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  subst x
  exact IsNilpotent.zero

theorem hasKernelExponent_id (n : ℕ) (hn : n ≠ 0) :
    HasKernelExponent (RingHom.id R) n := by
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  rw [hx0, zero_pow hn]

theorem isRostNilpotent_comp {f : R →+* S} {g : S →+* T}
    (hf : IsRostNilpotent f) (hg : IsRostNilpotent g) :
    IsRostNilpotent (g.comp f) := by
  intro x hx
  have hfx : IsNilpotent (f x) := hg (f x) (by simpa using hx)
  rcases hfx with ⟨n, hn⟩
  have hxpow : IsNilpotent (x ^ n) := by
    apply hf (x ^ n)
    simpa using hn
  exact IsNilpotent.of_pow hxpow

theorem isRostNilpotent_of_comp {f : R →+* S} {g : S →+* T}
    (h : IsRostNilpotent (g.comp f)) : IsRostNilpotent f := by
  intro x hx
  apply h x
  simp [hx]

theorem hasKernelExponent_comp {f : R →+* S} {g : S →+* T} {m n : ℕ}
    (hf : HasKernelExponent f m) (hg : HasKernelExponent g n) :
    HasKernelExponent (g.comp f) (n * m) := by
  intro x hx
  have hfxpow : f (x ^ n) = 0 := by
    simpa using hg (f x) (by simpa using hx)
  simpa [pow_mul] using hf (x ^ n) hfxpow

theorem hasKernelExponent_of_comp {f : R →+* S} {g : S →+* T} {n : ℕ}
    (h : HasKernelExponent (g.comp f) n) : HasKernelExponent f n := by
  intro x hx
  apply h x
  simp [hx]

theorem lift_idempotent_of_isRostNilpotent (f : R →+* S)
    (h : IsRostNilpotent f) (e : S) (he_range : e ∈ f.range)
    (he : IsIdempotentElem e) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e := by
  apply exists_isIdempotentElem_eq_of_ker_isNilpotent f
  · intro x hx
    exact h x (RingHom.mem_ker.mp hx)
  · exact he_range
  · exact he

theorem lift_orthogonal_idempotents_of_isRostNilpotent
    (f : R →+* S) {ι : Type*} [Finite ι] (h : IsRostNilpotent f)
    {e : ι → S} (he : OrthogonalIdempotents e)
    (he_range : ∀ i, e i ∈ f.range) :
    ∃ e' : ι → R, OrthogonalIdempotents e' ∧ f ∘ e' = e := by
  apply OrthogonalIdempotents.lift_of_isNilpotent_ker f
  · intro x hx
    exact h x (RingHom.mem_ker.mp hx)
  · exact he
  · exact he_range

theorem lift_completeOrthogonalIdempotents_of_isRostNilpotent
    (f : R →+* S) {ι : Type*} [Fintype ι] (h : IsRostNilpotent f)
    {e : ι → S} (he : CompleteOrthogonalIdempotents e)
    (he_range : ∀ i, e i ∈ f.range) :
    ∃ e' : ι → R, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
  apply CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker f
  · intro x hx
    exact h x (RingHom.mem_ker.mp hx)
  · exact he
  · exact he_range

end Rings

section Karoubi

variable {C : Type u₁} [Category.{v₁} C]

/-- Package an idempotent endomorphism as an object of the Karoubi envelope. -/
def karoubiObject (X : C) (p : End X) (hp : IsIdempotentElem p) :
    Idempotents.Karoubi C :=
  ⟨X, p, hp.eq⟩

@[simp]
theorem karoubiObject_X (X : C) (p : End X) (hp : IsIdempotentElem p) :
    (karoubiObject X p hp).X = X := rfl

@[simp]
theorem karoubiObject_p (X : C) (p : End X) (hp : IsIdempotentElem p) :
    (karoubiObject X p hp).p = p := rfl

end Karoubi

section AdditiveFunctors

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Preadditive C] [Preadditive D] [Preadditive E]

/-- The ring homomorphism on endomorphisms induced by an additive functor. -/
def endomorphismMapRingHom (F : C ⥤ D) [F.Additive] (X : C) :
    End X →+* End (F.obj X) :=
  RingHom.mk' (F.mapEnd X) fun _ _ => F.map_add

@[simp]
theorem endomorphismMapRingHom_apply (F : C ⥤ D) [F.Additive]
    (X : C) (f : End X) :
    endomorphismMapRingHom F X f = F.map f := rfl

@[simp]
theorem endomorphismMapRingHom_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (X : C) :
    endomorphismMapRingHom (F ⋙ G) X =
      (endomorphismMapRingHom G (F.obj X)).comp
        (endomorphismMapRingHom F X) := by
  ext f
  rfl

/-- Rost nilpotence for one object along an additive functor. -/
def IsRostNilpotentAt (F : C ⥤ D) [F.Additive] (X : C) : Prop :=
  IsRostNilpotent (endomorphismMapRingHom F X)

/-- A uniform kernel exponent for one object along an additive functor. -/
def HasKernelExponentAt (F : C ⥤ D) [F.Additive] (X : C) (n : ℕ) : Prop :=
  HasKernelExponent (endomorphismMapRingHom F X) n

/-- Rost nilpotence at every object of the source category. -/
def HasRostNilpotence (F : C ⥤ D) [F.Additive] : Prop :=
  ∀ X, IsRostNilpotentAt F X

theorem HasKernelExponentAt.isRostNilpotentAt
    (F : C ⥤ D) [F.Additive] (X : C) {n : ℕ}
    (h : HasKernelExponentAt F X n) :
    IsRostNilpotentAt F X :=
  h.isRostNilpotent

theorem isRostNilpotentAt_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (X : C)
    (hF : IsRostNilpotentAt F X)
    (hG : IsRostNilpotentAt G (F.obj X)) :
    IsRostNilpotentAt (F ⋙ G) X := by
  rw [IsRostNilpotentAt, endomorphismMapRingHom_comp]
  exact isRostNilpotent_comp hF hG

theorem isRostNilpotentAt_of_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (X : C)
    (h : IsRostNilpotentAt (F ⋙ G) X) :
    IsRostNilpotentAt F X := by
  rw [IsRostNilpotentAt, endomorphismMapRingHom_comp] at h
  exact isRostNilpotent_of_comp h

theorem hasKernelExponentAt_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (X : C) {m n : ℕ}
    (hF : HasKernelExponentAt F X m)
    (hG : HasKernelExponentAt G (F.obj X) n) :
    HasKernelExponentAt (F ⋙ G) X (n * m) := by
  rw [HasKernelExponentAt, endomorphismMapRingHom_comp]
  exact hasKernelExponent_comp hF hG

theorem hasRostNilpotence_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    (hF : HasRostNilpotence F) (hG : HasRostNilpotence G) :
    HasRostNilpotence (F ⋙ G) := by
  intro X
  exact isRostNilpotentAt_comp F G X (hF X) (hG (F.obj X))

theorem hasRostNilpotence_of_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    (h : HasRostNilpotence (F ⋙ G)) :
    HasRostNilpotence F := by
  intro X
  exact isRostNilpotentAt_of_comp F G X (h X)

theorem lift_projector_of_isRostNilpotentAt (F : C ⥤ D) [F.Additive]
    (X : C) (h : IsRostNilpotentAt F X)
    (e : End (F.obj X)) (he_range : e ∈ (endomorphismMapRingHom F X).range)
    (he : IsIdempotentElem e) :
    ∃ e' : End X, IsIdempotentElem e' ∧ F.map e' = e := by
  rcases lift_idempotent_of_isRostNilpotent
      (endomorphismMapRingHom F X) h e he_range he with ⟨e', he', hmap⟩
  exact ⟨e', he', hmap⟩

theorem exists_karoubiObject_lift_of_isRostNilpotentAt
    (F : C ⥤ D) [F.Additive] (X : C)
    (h : IsRostNilpotentAt F X)
    (e : End (F.obj X)) (he_range : e ∈ (endomorphismMapRingHom F X).range)
    (he : IsIdempotentElem e) :
    ∃ (p : End X) (hp : IsIdempotentElem p),
      F.map (karoubiObject X p hp).p = e := by
  rcases lift_projector_of_isRostNilpotentAt F X h e he_range he with
    ⟨p, hp, hmap⟩
  exact ⟨p, hp, hmap⟩

theorem lift_orthogonal_projector_family_of_isRostNilpotentAt
    (F : C ⥤ D) [F.Additive] (X : C)
    {ι : Type*} [Finite ι] (h : IsRostNilpotentAt F X)
    {e : ι → End (F.obj X)} (he : OrthogonalIdempotents e)
    (he_range : ∀ i, e i ∈ (endomorphismMapRingHom F X).range) :
    ∃ e' : ι → End X, OrthogonalIdempotents e' ∧ F.map ∘ e' = e := by
  rcases lift_orthogonal_idempotents_of_isRostNilpotent
      (endomorphismMapRingHom F X) h he he_range with ⟨e', he', hmap⟩
  exact ⟨e', he', hmap⟩

/-- Abstract motivic-decomposition lifting from a split complete projector family. -/
theorem lift_complete_projector_family_of_isRostNilpotentAt
    (F : C ⥤ D) [F.Additive] (X : C)
    {ι : Type*} [Fintype ι] (h : IsRostNilpotentAt F X)
    {e : ι → End (F.obj X)} (he : CompleteOrthogonalIdempotents e)
    (he_range : ∀ i, e i ∈ (endomorphismMapRingHom F X).range) :
    ∃ e' : ι → End X, CompleteOrthogonalIdempotents e' ∧ F.map ∘ e' = e := by
  rcases lift_completeOrthogonalIdempotents_of_isRostNilpotent
      (endomorphismMapRingHom F X) h he he_range with ⟨e', he', hmap⟩
  exact ⟨e', he', hmap⟩

end AdditiveFunctors

end RiemannResearch.Motives
