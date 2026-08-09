/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import RiemannResearch.CategoryTheory.PreadditiveIsoConjugation
import RiemannResearch.GroupCohomology.Corestriction

/-!
# Corestriction from an arbitrary finite-index subgroup

This file constructs additive first-cohomology corestriction from an arbitrary
finite-index subgroup. The transversal is indexed by left cosets and the
ambient group acts on that set. The resulting cochain formula sends cocycles
to cocycles and coboundaries to coboundaries, and hence descends to additive
H¹. Corestriction after restriction is multiplication by the subgroup index
without a normality hypothesis.
-/

open CategoryTheory
open scoped BigOperators

universe u

namespace RiemannResearch.GroupCohomology

/-- The chosen representative of a left coset. -/
noncomputable def leftCosetRepresentative
    {G : Type u} [Group G] (S : Subgroup G) : G ⧸ S → G :=
  Quotient.out

@[simp]
theorem leftCosetRepresentative_spec
    {G : Type u} [Group G] (S : Subgroup G) (q : G ⧸ S) :
    QuotientGroup.mk (leftCosetRepresentative S q) = q :=
  Quotient.out_eq' q

/-- The subgroup-valued defect of the chosen left-coset representatives. -/
noncomputable def leftCosetDefect
    {G : Type u} [Group G] (S : Subgroup G) (g : G) (q : G ⧸ S) : S :=
  ⟨(leftCosetRepresentative S q)⁻¹ * g *
      leftCosetRepresentative S (g⁻¹ • q), by
    rw [mul_assoc, ← QuotientGroup.eq]
    calc
      QuotientGroup.mk (leftCosetRepresentative S q) = q :=
        Quotient.out_eq' q
      _ = g • (g⁻¹ • q) := by simp
      _ = QuotientGroup.mk
          (g * leftCosetRepresentative S (g⁻¹ • q)) := by
        simpa only [leftCosetRepresentative, smul_eq_mul] using
          (MulAction.Quotient.mk_smul_out
            (H := S) g (g⁻¹ • q)).symm⟩

@[simp]
theorem coe_leftCosetDefect
    {G : Type u} [Group G] (S : Subgroup G) (g : G) (q : G ⧸ S) :
    ((leftCosetDefect S g q : S) : G) =
      (leftCosetRepresentative S q)⁻¹ * g *
        leftCosetRepresentative S (g⁻¹ • q) :=
  rfl

/-- Multiplying a representative by its defect gives the translated representative. -/
theorem leftCosetRepresentative_mul_defect
    {G : Type u} [Group G] (S : Subgroup G) (g : G) (q : G ⧸ S) :
    leftCosetRepresentative S q * (leftCosetDefect S g q : G) =
      g * leftCosetRepresentative S (g⁻¹ • q) := by
  simp [leftCosetDefect, mul_assoc]

/-- The left-coset defect is multiplicative in the ambient element. -/
theorem leftCosetDefect_mul
    {G : Type u} [Group G] (S : Subgroup G) (g h : G) (q : G ⧸ S) :
    leftCosetDefect S (g * h) q =
      leftCosetDefect S g q * leftCosetDefect S h (g⁻¹ • q) := by
  apply Subtype.ext
  simp only [coe_leftCosetDefect, Subgroup.coe_mul]
  rw [mul_inv_rev, mul_smul]
  simp [mul_assoc]

/-- One summand in arbitrary finite-index corestriction. -/
noncomputable def corestrictionSummand
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G)
    (z : S → A) (g : G) (q : G ⧸ S) : A :=
  (A.ρ (leftCosetRepresentative S q)) (z (leftCosetDefect S g q))

/-- Arbitrary finite-index corestriction on additive one-cochains. -/
noncomputable def corestrictionCochain
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex]
    (z : S → A) (g : G) : A := by
  letI := Fintype.ofFinite (G ⧸ S)
  exact ∑ q : G ⧸ S, corestrictionSummand A S z g q

/-- Arbitrary finite-index corestriction is linear on one-cochains. -/
noncomputable def corestrictionCochainLinearMap
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    (S → A) →ₗ[k] (G → A) where
  toFun := corestrictionCochain A S
  map_add' := by
    intro z w
    funext g
    simp [corestrictionCochain, corestrictionSummand,
      Finset.sum_add_distrib]
  map_smul' := by
    intro c z
    funext g
    simp only [corestrictionCochain, corestrictionSummand,
      Pi.smul_apply, map_smul]
    rw [Finset.smul_sum]
    simp

/-- The summand formula respects the additive cocycle identity. -/
theorem corestrictionSummand_mul
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G)
    (z : groupCohomology.cocycles₁ (Rep.res S.subtype A))
    (g h : G) (q : G ⧸ S) :
    corestrictionSummand A S z (g * h) q =
      (A.ρ g) (corestrictionSummand A S z h (g⁻¹ • q)) +
        corestrictionSummand A S z g q := by
  have hz :
      ∀ a b : S, z (a * b) =
        ((Rep.res S.subtype A).ρ a) (z b) + z a :=
    (groupCohomology.mem_cocycles₁_iff
      (A := Rep.res S.subtype A) z).mp z.property
  unfold corestrictionSummand
  rw [leftCosetDefect_mul, hz, map_add]
  congr 1
  change
    (A.ρ (leftCosetRepresentative S q))
      ((A.ρ (leftCosetDefect S g q : G))
        (z (leftCosetDefect S h (g⁻¹ • q)))) =
      (A.ρ g)
        ((A.ρ (leftCosetRepresentative S (g⁻¹ • q)))
          (z (leftCosetDefect S h (g⁻¹ • q))))
  rw [← Module.End.mul_apply, ← map_mul,
    leftCosetRepresentative_mul_defect, map_mul, Module.End.mul_apply]

/-- Arbitrary finite-index corestriction sends cocycles to cocycles. -/
theorem corestrictionCochain_mem_cocycles₁
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex]
    (z : groupCohomology.cocycles₁ (Rep.res S.subtype A)) :
    corestrictionCochain A S z ∈ groupCohomology.cocycles₁ A := by
  classical
  let _ := Fintype.ofFinite (G ⧸ S)
  apply (groupCohomology.mem_cocycles₁_iff
    (corestrictionCochain A S z)).2
  intro g h
  simp only [corestrictionCochain]
  simp_rw [corestrictionSummand_mul]
  rw [Finset.sum_add_distrib, map_sum]
  congr 1
  let e : (G ⧸ S) ≃ (G ⧸ S) :=
    Equiv.ofBijective (g⁻¹ • ·) (MulAction.bijective g⁻¹)
  simpa [e] using
    (Equiv.sum_comp e
      (fun q : G ⧸ S =>
        (A.ρ g) (corestrictionSummand A S z h q)))

/-- The transferred potential attached to a zero-cochain. -/
noncomputable def corestrictionPotential
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] (x : A) : A := by
  letI := Fintype.ofFinite (G ⧸ S)
  exact ∑ q : G ⧸ S, (A.ρ (leftCosetRepresentative S q)) x

/-- Corestriction of a coboundary is the coboundary of its transferred potential. -/
theorem corestrictionCochain_d₀₁_apply
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex]
    (x : A) (g : G) :
    corestrictionCochain A S
        ((groupCohomology.d₀₁ (Rep.res S.subtype A)).hom x) g =
      (groupCohomology.d₀₁ A).hom (corestrictionPotential A S x) g := by
  classical
  let _ := Fintype.ofFinite (G ⧸ S)
  unfold corestrictionCochain corestrictionPotential corestrictionSummand
  simp only [groupCohomology.d₀₁_hom_apply, MonoidHom.comp_apply, map_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [map_sum]
  let e : (G ⧸ S) ≃ (G ⧸ S) :=
    Equiv.ofBijective (g⁻¹ • ·) (MulAction.bijective g⁻¹)
  have hreindex := Equiv.sum_comp e
    (fun q : G ⧸ S =>
      (A.ρ g) ((A.ρ (leftCosetRepresentative S q)) x))
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Module.End.mul_apply, ← map_mul]
  change
    (A.ρ (leftCosetRepresentative S q *
      (leftCosetDefect S g q : G))) x =
      (A.ρ g) ((A.ρ (leftCosetRepresentative S (g⁻¹ • q))) x)
  rw [leftCosetRepresentative_mul_defect, map_mul, Module.End.mul_apply]

/-- Arbitrary finite-index corestriction sends coboundaries to coboundaries. -/
theorem corestrictionCochain_mem_coboundaries₁
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex]
    (z : groupCohomology.coboundaries₁ (Rep.res S.subtype A)) :
    corestrictionCochain A S z ∈ groupCohomology.coboundaries₁ A := by
  rcases z.property with ⟨x, hx⟩
  refine ⟨corestrictionPotential A S x, ?_⟩
  funext g
  rw [show (z : S → A) =
    (groupCohomology.d₀₁ (Rep.res S.subtype A)).hom x from hx.symm]
  exact (corestrictionCochain_d₀₁_apply A S x g).symm

/-- Arbitrary corestriction restricted to additive one-cocycles. -/
noncomputable def corestrictionCocyclesLinearMap
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    groupCohomology.cocycles₁ (Rep.res S.subtype A) →ₗ[k]
      groupCohomology.cocycles₁ A :=
  (corestrictionCochainLinearMap A S).restrict
    (fun z hz => corestrictionCochain_mem_cocycles₁ A S ⟨z, hz⟩)

/-- Cocycle corestriction maps subgroup coboundaries into ambient coboundaries. -/
theorem corestrictionCocyclesLinearMap_maps_toCyclesRange
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    (groupCohomology.shortComplexH1
      (Rep.res S.subtype A)).moduleCatToCycles.range ≤
      Submodule.comap (corestrictionCocyclesLinearMap A S)
        (groupCohomology.shortComplexH1 A).moduleCatToCycles.range := by
  intro z hz
  rcases hz with ⟨x, rfl⟩
  refine ⟨corestrictionPotential A S x, ?_⟩
  apply groupCohomology.cocycles₁_ext
  intro g
  exact (corestrictionCochain_d₀₁_apply A S x g).symm

/-- Arbitrary corestriction on explicit left-homology quotient modules. -/
noncomputable def corestrictionLeftHomologyLinearMap
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    ((groupCohomology.shortComplexH1
      (Rep.res S.subtype A)).moduleCatLeftHomologyData.H : Type u) →ₗ[k]
      ((groupCohomology.shortComplexH1 A).moduleCatLeftHomologyData.H : Type u) :=
  Submodule.mapQ
    (groupCohomology.shortComplexH1
      (Rep.res S.subtype A)).moduleCatToCycles.range
    (groupCohomology.shortComplexH1 A).moduleCatToCycles.range
    (corestrictionCocyclesLinearMap A S)
    (corestrictionCocyclesLinearMap_maps_toCyclesRange A S)

/-- Arbitrary corestriction on the explicit left-homology objects. -/
noncomputable def corestrictionLeftHomology
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    (groupCohomology.shortComplexH1
      (Rep.res S.subtype A)).moduleCatLeftHomologyData.H ⟶
      (groupCohomology.shortComplexH1 A).moduleCatLeftHomologyData.H :=
  ModuleCat.ofHom (corestrictionLeftHomologyLinearMap A S)

/-- Corestriction on additive H¹ from an arbitrary finite-index subgroup. -/
noncomputable def h1CorestrictionFiniteIndex
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    groupCohomology.H1 (Rep.res S.subtype A) ⟶ groupCohomology.H1 A :=
  (groupCohomology.H1Iso (Rep.res S.subtype A)).hom ≫
    corestrictionLeftHomology A S ≫ (groupCohomology.H1Iso A).inv

/-- The potential measuring transfer after restriction against index multiplication. -/
noncomputable def corestrictionRestrictionPotential
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex]
    (z : groupCohomology.cocycles₁ A) : A := by
  letI := Fintype.ofFinite (G ⧸ S)
  exact ∑ q : G ⧸ S, z (leftCosetRepresentative S q)

/-- Expand a transfer summand of a restricted ambient cocycle. -/
theorem corestrictionSummand_restrict
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G)
    (z : groupCohomology.cocycles₁ A) (g : G) (q : G ⧸ S) :
    corestrictionSummand A S (fun s : S => z s.1) g q =
      (A.ρ g) (z (leftCosetRepresentative S (g⁻¹ • q))) +
        z g - z (leftCosetRepresentative S q) := by
  have hz : ∀ a b : G, z (a * b) = (A.ρ a) (z b) + z a :=
    (groupCohomology.mem_cocycles₁_iff (A := A) z).mp z.property
  have h := hz (leftCosetRepresentative S q)
    (leftCosetDefect S g q : G)
  rw [leftCosetRepresentative_mul_defect,
    hz g (leftCosetRepresentative S (g⁻¹ • q))] at h
  unfold corestrictionSummand
  exact (eq_sub_iff_add_eq).2 h.symm

/-- Transfer after restriction differs from index multiplication by a coboundary. -/
theorem corestrictionCochain_restrict_apply
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex]
    (z : groupCohomology.cocycles₁ A) (g : G) :
    corestrictionCochain A S (fun s : S => z s.1) g =
      Nat.card (G ⧸ S) • z g +
        (ModuleCat.Hom.hom (groupCohomology.d₀₁ A))
          (corestrictionRestrictionPotential A S z) g := by
  classical
  let _ := Fintype.ofFinite (G ⧸ S)
  unfold corestrictionCochain corestrictionRestrictionPotential
  simp_rw [corestrictionSummand_restrict]
  simp only [groupCohomology.d₀₁_hom_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    map_sum, Finset.sum_const, Finset.card_univ]
  let e : (G ⧸ S) ≃ (G ⧸ S) :=
    Equiv.ofBijective (g⁻¹ • ·) (MulAction.bijective g⁻¹)
  have hreindex :
      (∑ q : G ⧸ S,
        (A.ρ g) (z (leftCosetRepresentative S (g⁻¹ • q)))) =
        ∑ q : G ⧸ S,
          (A.ρ g) (z (leftCosetRepresentative S q)) := by
    simpa [e] using
      (Equiv.sum_comp e
        (fun q : G ⧸ S =>
          (A.ρ g) (z (leftCosetRepresentative S q))))
  rw [hreindex, Nat.card_eq_fintype_card]
  abel

/-- On left-homology quotients, transfer after restriction is index multiplication. -/
theorem corestrictionLeftHomologyLinearMap_comp_restriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    (corestrictionLeftHomologyLinearMap A S).comp
      (restrictionLeftHomologyLinearMap A S) =
        Nat.card (G ⧸ S) • LinearMap.id := by
  apply RiemannResearch.LinearAlgebra.mapQ_comp_eq_nsmul_id
  intro z
  change groupCohomology.cocycles₁ A at z
  refine ⟨corestrictionRestrictionPotential A S z, ?_⟩
  apply groupCohomology.cocycles₁_ext
  intro g
  change
    (ModuleCat.Hom.hom (groupCohomology.d₀₁ A))
        (corestrictionRestrictionPotential A S z) g =
      corestrictionCochain A S (fun s : S => z s.1) g -
        Nat.card (G ⧸ S) • z g
  rw [corestrictionCochain_restrict_apply]
  abel

/-- On left-homology objects, transfer after restriction is index multiplication. -/
theorem restrictionLeftHomology_comp_corestriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    restrictionLeftHomology A S ≫ corestrictionLeftHomology A S =
      Nat.card (G ⧸ S) •
        𝟙 (groupCohomology.shortComplexH1 A).moduleCatLeftHomologyData.H := by
  ext x
  change
    (corestrictionLeftHomologyLinearMap A S)
        (restrictionLeftHomologyLinearMap A S x) =
      Nat.card (G ⧸ S) • x
  exact LinearMap.congr_fun
    (corestrictionLeftHomologyLinearMap_comp_restriction A S) x

/-- Restriction followed by arbitrary finite-index transfer is index multiplication on H¹. -/
theorem h1RestrictionViaCocycles_comp_h1CorestrictionFiniteIndex
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    h1RestrictionViaCocycles A S ≫ h1CorestrictionFiniteIndex A S =
      Nat.card (G ⧸ S) • 𝟙 (groupCohomology.H1 A) := by
  apply RiemannResearch.CategoryTheory.isoConjugate_comp_eq_nsmul_id
  exact restrictionLeftHomology_comp_corestriction A S

end RiemannResearch.GroupCohomology
