/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1
import RiemannResearch.GaloisCohomology.GaloisCechCoordinates

/-!
# Presheaf comparison for Galois Čech H¹

A generic cocycle-level comparison that descends to fixed-cover presheaf H¹.
The algebraic-geometric finite-Galois specialization lives in a bridge module.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u v

open CategoryTheory

universe w w' x y

/-- The exact comparison datum needed to identify Mathlib's fixed-cover
presheaf Čech cocycles with the finite-Galois coordinate cocycles.

For a representable group presheaf on a singleton finite Galois cover, the
first field is supplied by the Yoneda and affine-fiber-product
identifications. The second field records that those identifications carry
Mathlib's zero-cochain relation to the coordinate gauge relation. -/
structure PresheafGaloisCechComparison
    {C : Type w} [Category.{w'} C]
    (P : Cᵒᵖ ⥤ GrpCat.{x}) {I : Type y} (U : I → C)
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] where
  /-- Identification of fixed-cover presheaf cocycles with Galois-coordinate
  cocycles. -/
  cocycleEquiv :
    PresheafOfGroups.OneCocycle P U ≃ GaloisCechCocycle Γ G
  /-- The identification preserves and reflects the cohomology relation. -/
  cohomologous_iff : ∀ a b,
    a.IsCohomologous b ↔
      (cocycleEquiv a).Cohomologous (cocycleEquiv b)

namespace PresheafGaloisCechComparison

variable {C : Type w} [Category.{w'} C]
variable {P : Cᵒᵖ ⥤ GrpCat.{x}} {I : Type y} {U : I → C}
variable {Γ : Type u} {G : Type v} [Group Γ] [Group G]
variable [MulDistribMulAction Γ G]
variable (D : PresheafGaloisCechComparison P U Γ G)

private def rawH1Equiv :
    Quot (PresheafOfGroups.OneCocycle.IsCohomologous
      (G := P) (U := U)) ≃
      Quotient (GaloisCechCocycle.setoid Γ G) where
  toFun :=
    Quot.lift
      (fun a => GaloisCechH1.classOf (D.cocycleEquiv a))
      (by
        intro a b hab
        apply (Quotient.eq_iff_equiv).2
        exact (D.cohomologous_iff a b).mp hab)
  invFun :=
    Quotient.lift
      (fun a => (D.cocycleEquiv.symm a).class)
      (by
        intro a b hab
        change a.Cohomologous b at hab
        apply PresheafOfGroups.OneCocycle.IsCohomologous.class_eq
        apply (D.cohomologous_iff _ _).mpr
        simpa using hab)
  left_inv := by
    intro q
    refine Quot.inductionOn q ?_
    intro a
    change
      (D.cocycleEquiv.symm (D.cocycleEquiv a)).class = a.class
    rw [D.cocycleEquiv.symm_apply_apply]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    change
      GaloisCechH1.classOf
        (D.cocycleEquiv (D.cocycleEquiv.symm a)) =
        GaloisCechH1.classOf a
    rw [D.cocycleEquiv.apply_symm_apply]

/-- A cocycle-level comparison preserving the cohomology relation descends to
an equivalence between Mathlib's fixed-cover H¹ and coordinate Čech H¹. -/
def coordinateH1Equiv :
    PresheafOfGroups.H1 P U ≃ GaloisCechH1 Γ G :=
  D.rawH1Equiv

/-- A cocycle-level comparison preserving the cohomology relation descends to
the desired equivalence between Mathlib's fixed-cover H¹ and discrete
nonabelian H¹. -/
def h1EquivNonabelian :
    PresheafOfGroups.H1 P U ≃ NonabelianH1 Γ G :=
  D.coordinateH1Equiv.trans (GaloisCechH1.equivNonabelian Γ G)

/-- On a represented cocycle class, the comparison is the expected composite
of the coordinate cocycle equivalence and the group-cocycle equivalence. -/
@[simp]
theorem h1EquivNonabelian_class
    (a : PresheafOfGroups.OneCocycle P U) :
    D.h1EquivNonabelian a.class =
      NonabelianH1.classOf
        (galoisCechCocycleEquiv Γ G (D.cocycleEquiv a)) :=
  rfl

include D

/-- A fixed-cover comparison datum transfers the vanishing statement
(`H¹` is a singleton) exactly to discrete nonabelian `H¹`. This isolates
the abstract comparison input; `FiniteGaloisCechComparison` supplies its
canonical finite-Galois affine instance. -/
theorem subsingleton_h1_iff :
    Subsingleton (PresheafOfGroups.H1 P U) ↔
      Subsingleton (NonabelianH1 Γ G) := by
  let e := h1EquivNonabelian D
  constructor
  · intro h
    exact ⟨fun x y =>
      e.symm.injective (h.allEq (e.symm x) (e.symm y))⟩
  · intro h
    exact ⟨fun x y =>
      e.injective (h.allEq (e x) (e y))⟩

end PresheafGaloisCechComparison

end

end RiemannResearch.GaloisCohomology
