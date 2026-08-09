/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import RiemannResearch.LinearAlgebra.QuotientMap

/-!
# Explicit restriction in additive first group cohomology

Restriction on low-degree cocycles, explicit left-homology quotients, and the
induced additive H¹ map. Corestriction modules import this focused API.
-/

open CategoryTheory

universe u

namespace RiemannResearch.GroupCohomology

/-- Restriction of additive one-cocycles to a subgroup, in the explicit
low-degree cocycle model. -/
noncomputable def restrictionCocyclesLinearMap
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) :
    groupCohomology.cocycles₁ A →ₗ[k]
      groupCohomology.cocycles₁ (Rep.res S.subtype A) :=
  ModuleCat.Hom.hom
    (groupCohomology.mapCocycles₁ S.subtype
      (𝟙 (Rep.res S.subtype A)))

@[simp]
theorem restrictionCocyclesLinearMap_apply
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G)
    (z : groupCohomology.cocycles₁ A) (s : S) :
    restrictionCocyclesLinearMap A S z s = z s.1 := by
  rw [restrictionCocyclesLinearMap,
    groupCohomology.coe_mapCocycles₁]
  rfl

/-- Explicit cocycle restriction sends ambient coboundaries to subgroup
coboundaries. -/
theorem restrictionCocyclesLinearMap_maps_toCyclesRange
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) :
    (groupCohomology.shortComplexH1 A).moduleCatToCycles.range ≤
      Submodule.comap (restrictionCocyclesLinearMap A S)
        (groupCohomology.shortComplexH1
          (Rep.res S.subtype A)).moduleCatToCycles.range := by
  intro z hz
  rcases hz with ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  apply groupCohomology.cocycles₁_ext
  intro s
  rfl

/-- Restriction on the explicit left-homology quotient computing additive
first group cohomology. -/
noncomputable def restrictionLeftHomologyLinearMap
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) :
    ((groupCohomology.shortComplexH1 A).moduleCatLeftHomologyData.H :
      Type u) →ₗ[k]
      ((groupCohomology.shortComplexH1
        (Rep.res S.subtype A)).moduleCatLeftHomologyData.H : Type u) :=
  Submodule.mapQ
    (groupCohomology.shortComplexH1 A).moduleCatToCycles.range
    (groupCohomology.shortComplexH1
      (Rep.res S.subtype A)).moduleCatToCycles.range
    (restrictionCocyclesLinearMap A S)
    (restrictionCocyclesLinearMap_maps_toCyclesRange A S)

/-- Restriction as a morphism between the explicit left-homology objects. -/
noncomputable def restrictionLeftHomology
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) :
    (groupCohomology.shortComplexH1 A).moduleCatLeftHomologyData.H ⟶
      (groupCohomology.shortComplexH1
        (Rep.res S.subtype A)).moduleCatLeftHomologyData.H :=
  ModuleCat.ofHom (restrictionLeftHomologyLinearMap A S)

/-- Restriction on additive `H¹` obtained directly from the explicit
low-degree cocycle quotient. -/
noncomputable def h1RestrictionViaCocycles
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) :
    groupCohomology.H1 A ⟶
      groupCohomology.H1 (Rep.res S.subtype A) :=
  (groupCohomology.H1Iso A).hom ≫
    restrictionLeftHomology A S ≫
      (groupCohomology.H1Iso (Rep.res S.subtype A)).inv

end RiemannResearch.GroupCohomology
