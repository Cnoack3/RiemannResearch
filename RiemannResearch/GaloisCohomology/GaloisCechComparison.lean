/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcCechH1
import RiemannResearch.GaloisCohomology.GaloisCechCoordinates

/-!
# Presheaf and fpqc comparison for Galois Čech H¹

This module packages the cocycle-level coordinate equivalence into presheaf
Čech H¹ and specializes it to singleton finite-Galois fpqc covers. The tensor
coordinates and coordinate cocycle quotient live in `GaloisCechCoordinates`.
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

end PresheafGaloisCechComparison

end

end RiemannResearch.GaloisCohomology


namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
open RiemannResearch.GaloisCohomology

universe u₁ v₁ w₁ x₁

noncomputable section

/-- The morphism Spec L → Spec K associated to a finite Galois field
extension. -/
def finiteGaloisCoverHom
    (K L : Type u₁) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    _root_.AlgebraicGeometry.Spec (CommRingCat.of L) ⟶
      _root_.AlgebraicGeometry.Spec (CommRingCat.of K) :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap K L))

/-- A finite Galois field extension gives a singleton fpqc cover
Spec L → Spec K. Flatness, surjectivity, and quasi-compactness are supplied by
Mathlib from finite-dimensionality and affineness. -/
def finiteGaloisFpqcCover
    (K L : Type u₁) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    FpqcCover (CommRingCat.of K) PUnit :=
  FpqcCover.singleton (finiteGaloisCoverHom K L)

/-- The cocycle-level comparison datum specialized to an affine group scheme
on a fixed fpqc cover. Constructing this datum for Spec L → Spec K is exactly
the remaining Yoneda and affine-fiber-product representability step. -/
abbrev FpqcGaloisCechComparison
    (R A : CommRingCat.{u₁}) [HopfAlgebra R A]
    {I : Type v₁} (U : FpqcCover R I)
    (Γ : Type w₁) (G : Type x₁) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] :=
  PresheafGaloisCechComparison
    (affineGroupPresheaf R A) U.obj Γ G

namespace FpqcGaloisCechComparison

variable (R A : CommRingCat.{u₁}) [HopfAlgebra R A]
variable {I : Type v₁} (U : FpqcCover R I)
variable (Γ : Type w₁) (G : Type x₁) [Group Γ] [Group G]
variable [MulDistribMulAction Γ G]

/-- Once the affine fixed-cover cocycle comparison datum is supplied, it
descends without further hypotheses to an equivalence from fixed-cover fpqc
Čech H¹ to discrete nonabelian H¹. -/
def h1EquivNonabelian
    (D : FpqcGaloisCechComparison R A U Γ G) :
    FpqcCechH1 R A U ≃ NonabelianH1 Γ G :=
  PresheafGaloisCechComparison.h1EquivNonabelian D

end FpqcGaloisCechComparison

/-- For the singleton finite Galois fpqc cover, an explicit cocycle-level
Yoneda comparison datum yields the desired fixed-cover Čech/Galois H¹
equivalence. The datum is the remaining representability obligation. -/
def finiteGaloisH1EquivNonabelian
    (K L : Type u₁) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (A : CommRingCat.{u₁}) [HopfAlgebra (CommRingCat.of K) A]
    (G : Type x₁) [Group G]
    [MulDistribMulAction (L ≃ₐ[K] L) G]
    (D : FpqcGaloisCechComparison
      (CommRingCat.of K) A (finiteGaloisFpqcCover K L)
      (L ≃ₐ[K] L) G) :
    FpqcCechH1 (CommRingCat.of K) A
        (finiteGaloisFpqcCover K L) ≃
      NonabelianH1 (L ≃ₐ[K] L) G :=
  FpqcGaloisCechComparison.h1EquivNonabelian
    (CommRingCat.of K) A (finiteGaloisFpqcCover K L)
      (L ≃ₐ[K] L) G D

end

end RiemannResearch.AlgebraicGeometry
