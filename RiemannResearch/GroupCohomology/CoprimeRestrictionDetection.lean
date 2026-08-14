/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GroupCohomology.ArbitraryCorestriction
import RiemannResearch.GroupTheory.CoprimeRestriction

/-!
# Detection by subgroup restrictions of coprime index

This module combines arbitrary finite-index corestriction with integral
Bézout descent. A finite family of subgroup restrictions whose indices have
gcd one jointly detects zero in additive first group cohomology.

In the E8 Serre II application this is the abelian middle step after a
simultaneous gauge has put a nonabelian cocycle in one Galois-stable Borel:
the residual torus class restricts trivially to all subsystem stabilizers, so
coprime-index detection kills it globally.

Source: user-provided Research Target 7.1 analysis (14 August 2026); the source
supports the application and proof strategy. The proof itself uses the
kernel-checked arbitrary corestriction formula already in this repository.
-/

open CategoryTheory

universe u v

namespace RiemannResearch.GroupCohomology

open RiemannResearch.GroupTheory

/-- A finite family of subgroup restrictions with gcd-one indices jointly
detects zero in additive H¹. -/
theorem h1_eq_zero_of_gcd_one_restrictions
    {k G : Type u} [CommRing k] [Group G]
    {ι : Type v} (A : Rep k G) (S : ι → Subgroup G)
    [∀ i, (S i).FiniteIndex]
    (s : Finset ι)
    (hgcd : s.gcd (fun i => (Nat.card (G ⧸ S i) : ℤ)) = 1)
    {x : groupCohomology.H1 A}
    (hres : ∀ i ∈ s, h1RestrictionViaCocycles A (S i) x = 0) :
    x = 0 := by
  apply eq_zero_of_gcd_one_annihilators
    s (fun i => Nat.card (G ⧸ S i)) hgcd
  intro i hi
  have hcomp :=
    h1RestrictionViaCocycles_comp_h1CorestrictionFiniteIndex A (S i)
  have happ := congrArg
    (fun f : groupCohomology.H1 A ⟶ groupCohomology.H1 A => f x) hcomp
  simpa [hres i hi] using happ.symm

/-- The joint restriction map to a finite gcd-one family of subgroups is
injective on additive H¹. -/
theorem h1_restrictionFamily_injective_of_gcd_one
    {k G : Type u} [CommRing k] [Group G]
    {ι : Type v} (A : Rep k G) (S : ι → Subgroup G)
    [∀ i, (S i).FiniteIndex]
    (s : Finset ι)
    (hgcd : s.gcd (fun i => (Nat.card (G ⧸ S i) : ℤ)) = 1) :
    Function.Injective
      (fun x : groupCohomology.H1 A =>
        fun i : ↥s => h1RestrictionViaCocycles A (S i.1) x) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply h1_eq_zero_of_gcd_one_restrictions A S s hgcd
  intro i hi
  rw [map_sub]
  apply sub_eq_zero.mpr
  have hi' := congrFun hxy ⟨i, hi⟩
  simpa using hi'

end RiemannResearch.GroupCohomology
