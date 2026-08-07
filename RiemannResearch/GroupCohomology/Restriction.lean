/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Restriction in additive first group cohomology

This module packages Mathlib's functorial map on additive group cohomology as
an `H¹` restriction map. It also records identity, composition, and nested
subgroup compatibility.

This is additive group cohomology with coefficients in a representation. It
does not construct a restriction or corestriction operation for nonabelian
Galois cohomology.
-/

open CategoryTheory

universe u

namespace RiemannResearch.GroupCohomology

/-- Restriction on additive `H¹` along a group homomorphism. -/
noncomputable def h1RestrictionAlong
    {k G H : Type u} [CommRing k] [Group G] [Group H]
    (A : Rep k H) (f : G →* H) :
    groupCohomology.H1 A ⟶ groupCohomology.H1 (Rep.res f A) :=
  groupCohomology.map f (𝟙 _) 1

/-- Restriction on additive `H¹` from a group to a subgroup. -/
noncomputable def h1Restriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) :
    groupCohomology.H1 A ⟶
      groupCohomology.H1 (Rep.res H.subtype A) :=
  h1RestrictionAlong A H.subtype

/-- The `H¹` map associated with identity maps on the group and coefficients
is the identity. -/
@[simp]
theorem h1Restriction_id
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) :
    groupCohomology.map (MonoidHom.id G) (𝟙 A) 1 = 𝟙 _ :=
  groupCohomology.map_id 1

/-- Restriction along a composite group homomorphism is the composite of the
two restriction maps. The coefficient morphism on the left identifies the
one-step restriction with the iterated restriction representation. -/
theorem h1RestrictionAlong_comp
    {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    (A : Rep k K) (f : H →* K) (g : G →* H) :
    groupCohomology.map (f.comp g)
        (Rep.resMap g (𝟙 (Rep.res f A))) 1 =
      h1RestrictionAlong A f ≫
        h1RestrictionAlong (Rep.res f A) g := by
  simpa [h1RestrictionAlong] using
    (groupCohomology.map_comp f g (𝟙 _) (𝟙 _) 1)

/-- For nested subgroups `K ≤ H ≤ G`, direct restriction from `G` to `K`
equals restriction first to `H` and then along the inclusion `K → H`. -/
theorem h1Restriction_tower
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) {K H : Subgroup G} (hKH : K ≤ H) :
    h1Restriction A K =
      h1Restriction A H ≫
        h1RestrictionAlong (Rep.res H.subtype A)
          (Subgroup.inclusion hKH) := by
  change groupCohomology.map K.subtype (𝟙 (Rep.res K.subtype A)) 1 =
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 1 ≫
      groupCohomology.map (Subgroup.inclusion hKH)
        (𝟙 (Rep.res (Subgroup.inclusion hKH) (Rep.res H.subtype A))) 1
  let middle :
      groupCohomology.H1 A ⟶ groupCohomology.H1 (Rep.res K.subtype A) :=
    groupCohomology.map
      (H.subtype.comp (Subgroup.inclusion hKH))
      (Rep.resMap (Subgroup.inclusion hKH)
          (𝟙 (Rep.res H.subtype A)) ≫
        𝟙 (Rep.res (Subgroup.inclusion hKH)
          (Rep.res H.subtype A))) 1
  have hdirect :
      groupCohomology.map K.subtype (𝟙 (Rep.res K.subtype A)) 1 =
        middle := by
    dsimp [middle]
    apply groupCohomology.map_congr
    · exact (Subgroup.subtype_comp_inclusion hKH).symm
    · ext x
      rfl
  have hcomp :
      middle =
        groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 1 ≫
          groupCohomology.map (Subgroup.inclusion hKH)
            (𝟙 (Rep.res (Subgroup.inclusion hKH)
              (Rep.res H.subtype A))) 1 := by
    dsimp [middle]
    exact groupCohomology.map_comp H.subtype
      (Subgroup.inclusion hKH) (𝟙 _) (𝟙 _) 1
  exact hdirect.trans hcomp

end RiemannResearch.GroupCohomology
