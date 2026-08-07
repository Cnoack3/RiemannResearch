/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GroupCohomology.Restriction

/-!
# A finite-index injectivity case for additive first group cohomology

For a finite group whose order is a unit in the coefficient ring, averaging
shows directly that every additive one-cocycle is a coboundary. Combining this
with Mathlib's inflation--restriction exact sequence proves that restriction
to a normal finite-index subgroup is injective when its index is a unit.

Brown's full stable-elements theorem applies to arbitrary subgroups and
identifies the image of restriction. That stronger result requires a
cohomological transfer and its double-coset formula. Mathlib currently exposes
neither construction for group cohomology, so this module records the strongest
case supplied by its present inflation--restriction API without assuming a
restriction--corestriction identity.
-/

open CategoryTheory
open scoped BigOperators

universe u

namespace RiemannResearch.GroupCohomology

/-- If the order of a finite group is a unit in the coefficient ring, every
additive one-cocycle is a coboundary.

The witness is the usual average
`-(|G|⁻¹) • ∑ g, z g`, with the inverse represented by a unit of the ring.
-/
theorem cocycle_mem_coboundaries_of_isUnit_fintype_card
    {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (hcard : IsUnit (Fintype.card G : k))
    (z : groupCohomology.cocycles₁ A) :
    (z : G → A) ∈ groupCohomology.coboundaries₁ A := by
  classical
  obtain ⟨cardUnit, hcardUnit⟩ := hcard
  let total : A := ∑ h : G, z h
  let n : k := Fintype.card G
  let nInv : k := ↑cardUnit⁻¹
  have hz :
      ∀ g h : G, z (g * h) = (A.ρ g) (z h) + z g :=
    (groupCohomology.mem_cocycles₁_iff (A := A) z).mp z.property
  refine ⟨-(nInv • total), ?_⟩
  funext g
  rw [groupCohomology.d₀₁_hom_apply]
  have hperm : (∑ h : G, z (g * h)) = total := by
    simpa [total] using
      (Equiv.sum_comp (Equiv.mulLeft g) (fun h => z h))
  have hcocycle_sum :
      (A.ρ g) total + Fintype.card G • z g = total := by
    calc
      (A.ρ g) total + Fintype.card G • z g =
          (∑ h : G, (A.ρ g) (z h)) + ∑ _h : G, z g := by
            simp [total]
      _ = ∑ h : G, ((A.ρ g) (z h) + z g) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ h : G, z (g * h) :=
        Fintype.sum_congr _ _ fun h => (hz g h).symm
      _ = total := hperm
  have hscalar :
      n • z g = total - (A.ρ g) total := by
    change (Fintype.card G : k) • z g =
      total - (A.ρ g) total
    rw [Nat.cast_smul_eq_nsmul]
    exact eq_sub_of_add_eq' hcocycle_sum
  calc
    (A.ρ g) (-(nInv • total)) - (-(nInv • total)) =
        nInv • (total - (A.ρ g) total) := by
          simp [sub_eq_add_neg, add_comm]
    _ = nInv • (n • z g) := by rw [hscalar]
    _ = (nInv * n) • z g := by rw [smul_smul]
    _ = z g := by
      have hinv : nInv * n = 1 := by
        simp [nInv, n, ← hcardUnit]
      rw [hinv, one_smul]

/-- Additive first group cohomology of a finite group vanishes when the group
order is a unit in the coefficient ring. -/
theorem h1_subsingleton_of_isUnit_fintype_card
    {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (hcard : IsUnit (Fintype.card G : k)) :
    Subsingleton (groupCohomology.H1 A) := by
  have hsurjective :
      Function.Surjective
        (ConcreteCategory.hom (groupCohomology.H1π A)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hzero : ∀ x : groupCohomology.H1 A, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := hsurjective x
    exact (groupCohomology.H1π_eq_zero_iff z).2
      (cocycle_mem_coboundaries_of_isUnit_fintype_card A hcard z)
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- In an exact short complex of modules, the second map is injective if the
source of the first map is subsingleton. -/
theorem shortComplex_g_injective_of_exact_of_subsingleton
    {k : Type u} [Ring k]
    (C : ShortComplex (ModuleCat k)) (hC : C.Exact)
    [Subsingleton C.X₁] :
    Function.Injective (ConcreteCategory.hom C.g) := by
  intro x y hxy
  have hker :
      ConcreteCategory.hom C.g (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ :=
    (ShortComplex.moduleCat_exact_iff C).mp hC (x - y) hker
  have hz0 : z = 0 := Subsingleton.elim _ _
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-- Restriction on additive `H¹` to a normal finite-index subgroup is
injective when the subgroup index is a unit in the coefficient ring.

This is the inflation--restriction case of finite-index restriction
injectivity. It does not use or assume a cohomological transfer.
-/
theorem h1Restriction_injective_of_normal_finiteIndex
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (hindex : IsUnit (S.index : k)) :
    Function.Injective (h1Restriction A S) := by
  let _ := Fintype.ofFinite (G ⧸ S)
  have hquotientCard :
      IsUnit (Fintype.card (G ⧸ S) : k) := by
    simpa [S.index_eq_card, Nat.card_eq_fintype_card] using hindex
  let _ :
      Subsingleton (groupCohomology.H1InfRes A S).X₁ := by
    change Subsingleton
      (groupCohomology.H1
        (Rep.of (A.ρ.quotientToInvariants S)))
    exact h1_subsingleton_of_isUnit_fintype_card
      (Rep.of (A.ρ.quotientToInvariants S)) hquotientCard
  change Function.Injective
    (ConcreteCategory.hom (groupCohomology.H1InfRes A S).g)
  exact shortComplex_g_injective_of_exact_of_subsingleton
    (groupCohomology.H1InfRes A S)
    (groupCohomology.H1InfRes_exact A S)

end RiemannResearch.GroupCohomology
