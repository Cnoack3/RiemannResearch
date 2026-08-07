/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# fpqc torsors under group objects

This module defines fpqc torsors in the slice category of schemes. A torsor is
a module object whose action is simply transitive and whose structure morphism
is faithfully flat and quasi-compact.

The general-purpose first part proves the internal analogue of the familiar
fact that a chosen point trivializes a torsor: the orbit map of a point of a
simply transitive module object is an equivariant isomorphism from the regular
module. The final declaration specializes this construction to fpqc torsors
of schemes.

This module does not yet prove effective fpqc descent or identify isomorphism
classes of torsors with the global nonabelian Čech `H¹` carrier.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.ModObj

universe u v

private theorem generalized_mul_smul
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
    {G P Z : C} [MonObj G] [ModObj G P]
    (m n : Z ⟶ G) (q : Z ⟶ P) :
    (m * n) • q = m • (n • q) := by
  simp only [mul_smul]

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
variable {G P : C} [MonObj G] [ModObj G P]

/-- The orbit map determined by a global point of an internal module object. -/
def orbitMap (p : 𝟙_ C ⟶ P) : G ⟶ P :=
  (𝟙 G) • (toUnit G ≫ p)

/-- Precomposition with an orbit map is pointwise scalar multiplication of
the chosen global point. -/
@[reassoc]
theorem comp_orbitMap (p : 𝟙_ C ⟶ P) {Z : C} (g : Z ⟶ G) :
    g ≫ orbitMap (G := G) p = g • (toUnit Z ≫ p) := by
  rw [orbitMap, ModObj.comp_smul]
  simp

/-- The orbit map is equivariant for the regular action on the source. -/
instance orbitMap_isModHom (p : 𝟙_ C ⟶ P) :
    let _ : ModObj G G := ModObj.regular G
    IsModHom G (orbitMap (G := G) p) := by
  let _ : ModObj G G := ModObj.regular G
  refine { smul_hom := ?_ }
  apply (yoneda (C := C)).map_injective
  ext Z z
  change z ≫ γ[G, G] ≫ orbitMap (G := G) p =
    z ≫ (G ◁ orbitMap (G := G) p) ≫ γ[G, P]
  let m : Z.unop ⟶ G := z ≫ fst G G
  let n : Z.unop ⟶ G := z ≫ snd G G
  let q : Z.unop ⟶ P := toUnit Z.unop ≫ p
  have hz : z = lift m n := by
    dsimp [m, n]
    simp
  have hzmul : z ≫ γ[G, G] = m * n := by
    rw [hz]
    simp [CategoryTheory.Hom.mul_def]
  have hzrhs :
      z ≫ (G ◁ orbitMap (G := G) p) ≫ γ[G, P] =
        m • (n • q) := by
    rw [hz]
    simp [orbitMap, CategoryTheory.Hom.smul_def, q]
  calc
    z ≫ γ[G, G] ≫ orbitMap (G := G) p =
        (m * n) ≫ orbitMap (G := G) p := by
          rw [← Category.assoc, hzmul]
    _ = (m * n) • q := by
      simpa [q] using comp_orbitMap (G := G) (P := P) p (m * n)
    _ = m • (n • q) := generalized_mul_smul m n q
    _ = z ≫ (G ◁ orbitMap (G := G) p) ≫ γ[G, P] := hzrhs.symm

/-- A global point of a simply transitive internal module object has an
isomorphic orbit map. -/
theorem isIso_orbitMap
    (h : IsIso (leftSMul G P)) (p : 𝟙_ C ⟶ P) :
    IsIso (orbitMap (G := G) p) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro Z
  rw [Function.bijective_iff_existsUnique]
  intro y
  have hs := (isIso_leftSMul_iff.mp h) Z (toUnit Z ≫ p) y
  simpa only [comp_orbitMap (G := G) (P := P)] using hs

/-- A chosen global point trivializes a simply transitive internal module
object, equivariantly for the acting monoid. -/
noncomputable def orbitModIso
    (h : IsIso (leftSMul G P)) (p : 𝟙_ C ⟶ P) :
    Mod.regular G ≅ Mod.mk P := by
  letI : ModObj G G := ModObj.regular G
  letI : IsIso (orbitMap (G := G) p) := isIso_orbitMap h p
  let e := asIso (orbitMap (G := G) p)
  let hhom : IsModHom G e.hom := by
    dsimp [e]
    exact orbitMap_isModHom p
  letI : IsModHom G e.hom := hhom
  let hinv : IsModHom G e.inv := inferInstance
  let hom : Mod.regular G ⟶ Mod.mk P :=
    Mod.Hom.mk'' e.hom hhom.smul_hom
  let inv : Mod.mk P ⟶ Mod.regular G :=
    Mod.Hom.mk'' e.inv hinv.smul_hom
  exact
    { hom := hom
      inv := inv
      hom_inv_id := Mod.hom_ext _ _ e.hom_inv_id
      inv_hom_id := Mod.hom_ext _ _ e.inv_hom_id }

end CategoryTheory.ModObj

namespace RiemannResearch.AlgebraicGeometry

/-- A group action is simply transitive when the canonical map
`G × P ⟶ P × P` is an isomorphism. -/
def IsSimplyTransitive
    (X : _root_.AlgebraicGeometry.Scheme.{u})
    (G : Over X) [GrpObj G]
    (P : CategoryTheory.Mod (Over X) G) : Prop :=
  let _ : ModObj G P.X := P.mod
  IsIso (ModObj.leftSMul G P.X)

/-- An fpqc torsor is a simply transitive group action whose structure
morphism is flat, surjective, and quasi-compact. -/
def IsFpqcTorsor
    (X : _root_.AlgebraicGeometry.Scheme.{u})
    (G : Over X) [GrpObj G]
    (P : CategoryTheory.Mod (Over X) G) : Prop :=
  IsSimplyTransitive X G P ∧
    _root_.AlgebraicGeometry.Flat P.X.hom ∧
    _root_.AlgebraicGeometry.Surjective P.X.hom ∧
    _root_.AlgebraicGeometry.QuasiCompact P.X.hom

/-- The full subcategory of fpqc torsors under `G` over `X`. -/
abbrev FpqcTorsor
    (X : _root_.AlgebraicGeometry.Scheme.{u})
    (G : Over X) [GrpObj G] :=
  ObjectProperty.FullSubcategory (IsFpqcTorsor X G)

/-- Simple transitivity is equivalent to existence and uniqueness of the
group element carrying any generalized point of the torsor to any other. -/
theorem isSimplyTransitive_iff
    (X : _root_.AlgebraicGeometry.Scheme.{u})
    (G : Over X) [GrpObj G]
    (P : CategoryTheory.Mod (Over X) G) :
    IsSimplyTransitive X G P ↔
      ∀ (Z : Over X) (x y : Z ⟶ P.X),
        ∃! m : Z ⟶ G, m • x = y := by
  let _ : ModObj G P.X := P.mod
  exact ModObj.isIso_leftSMul_iff

/-- A global section of an fpqc torsor produces an equivariant
trivialization by the regular torsor. This is the scheme-level
section-to-trivialization half of the torsor/Čech-`H¹` classification. -/
noncomputable def fpqcTorsorTrivializationOfSection
    (X : _root_.AlgebraicGeometry.Scheme.{u})
    (G : Over X) [GrpObj G]
    (P : CategoryTheory.Mod (Over X) G)
    (hP : IsFpqcTorsor X G P)
    (p : 𝟙_ (Over X) ⟶ P.X) :
    Mod.regular G ≅ P :=
  ModObj.orbitModIso hP.1 p

end RiemannResearch.AlgebraicGeometry
