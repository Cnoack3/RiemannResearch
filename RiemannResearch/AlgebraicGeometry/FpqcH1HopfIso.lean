/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.HopfFpqcH1Action

/-!
# Global fpqc H¹ under Hopf-algebra isomorphisms

A morphism between the affine group presheaves represented by two Hopf
algebras over the same base acts on global fpqc Čech `H¹`. An isomorphism of
presheaves therefore gives an equivalence of global `H¹` sets, preserving the
neutral class.

This is the coefficient-changing version of the endomorphism functoriality in
`FpqcH1Functoriality`.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

noncomputable section

universe u v

namespace FpqcH1

variable {R A B : CommRingCat.{u}}
variable [HopfAlgebra R A] [HopfAlgebra R B]

/-- A morphism between represented affine group presheaves over a fixed base
acts on global fpqc Čech `H¹`. -/
def mapOfPresheafHom
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B) :
    FpqcH1.{u, v} R A → FpqcH1.{u, v} R B :=
  Quotient.map
    (fun a =>
      { I := a.I
        cover := a.cover
        value := PresheafH1.map (U := a.cover.obj) η a.value })
    (by
      intro a b h
      rcases h with ⟨K, W, ra, rb, hab⟩
      refine ⟨K, W, ra, rb, ?_⟩
      rw [← ra.map_pullbackH1, ← rb.map_pullbackH1]
      exact congrArg (PresheafH1.map η) hab)

/-- The global map is represented coverwise by the usual map on fixed-cover
Čech `H¹`. -/
@[simp] theorem mapOfPresheafHom_classOf
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B)
    {I : Type v} (U : FpqcCover R I) (ξ : FpqcCechH1 R A U) :
    mapOfPresheafHom η (classOf R A U ξ) =
      classOf R B U (PresheafH1.map η ξ) :=
  rfl

/-- Every morphism of represented affine group presheaves preserves the
neutral global fpqc class. -/
@[simp] theorem mapOfPresheafHom_neutral
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B) :
    mapOfPresheafHom η (neutral R A) = neutral R B := by
  rw [neutral, mapOfPresheafHom_classOf,
    FpqcCechH1.neutral_eq_one, PresheafH1.map_one,
    ← FpqcCechH1.neutral_eq_one]
  rfl

/-- An isomorphism of represented affine group presheaves induces an
equivalence on global fpqc Čech `H¹`. -/
def equivOfPresheafIso
    (e : affineGroupPresheaf R A ≅ affineGroupPresheaf R B) :
    FpqcH1.{u, v} R A ≃ FpqcH1.{u, v} R B where
  toFun := mapOfPresheafHom e.hom
  invFun := mapOfPresheafHom e.inv
  left_inv x := by
    refine Quotient.inductionOn x ?_
    rintro ⟨I, U, ξ⟩
    change classOf R A U
      (PresheafH1.map e.inv (PresheafH1.map e.hom ξ)) =
        classOf R A U ξ
    exact congrArg (classOf R A U)
      ((PresheafH1.equiv (U := U.obj) e).left_inv ξ)
  right_inv x := by
    refine Quotient.inductionOn x ?_
    rintro ⟨I, U, ξ⟩
    change classOf R B U
      (PresheafH1.map e.hom (PresheafH1.map e.inv ξ)) =
        classOf R B U ξ
    exact congrArg (classOf R B U)
      ((PresheafH1.equiv (U := U.obj) e).right_inv ξ)

/-- The fpqc `H¹` equivalence induced by a presheaf isomorphism sends the
neutral class to the neutral class. -/
@[simp] theorem equivOfPresheafIso_neutral
    (e : affineGroupPresheaf R A ≅ affineGroupPresheaf R B) :
    equivOfPresheafIso e (neutral R A) = neutral R B :=
  mapOfPresheafHom_neutral e.hom

end FpqcH1

end

end RiemannResearch.AlgebraicGeometry
