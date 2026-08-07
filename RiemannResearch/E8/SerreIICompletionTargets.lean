/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.ZMod.Basic
import RiemannResearch.GaloisCohomology.LocalGaugeTransporter
import RiemannResearch.GroupTheory.CoprimeRestriction
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Conditional completion targets for the E8 case of Serre II

This module kernel-checks three implication patterns isolated in the
5 August 2026 E8 Serre II memorandum:

* odd-degree point descent plus odd-degree splitting proves neutrality;
* a common gauge on a generating family proves that a nonabelian cocycle is a
  global coboundary;
* the single diagonal kernel-norm value, together with the
  restriction--corestriction degree formula and a positive Bezout congruence,
  proves neutrality.

The finite-etale formulation below makes the last input explicit as a
componentwise neutral tuple. A concrete `ZMod 2` countermodel shows that the
additive transfer and Bezout identities alone cannot prove that this tuple's
corestriction remains in the neutral fiber.

These are conditional assembly theorems. They do not prove odd-degree descent,
existence of compatible E8 gauges, or the diagonal E8 kernel-norm hypothesis.
-/

universe u v w

namespace RiemannResearch.E8

open RiemannResearch.GaloisCohomology
open RiemannResearch.GaloisCohomology.NonabelianCocycle

/-- **Completion target A.** If every candidate class is neutral over some
odd-degree extension, points are equivalent to neutrality over every
extension, and points descend along those odd-degree extensions, then every
candidate is neutral over the base.

The point predicate can be instantiated by the E8 Borel variety, the EVIII
variety, or the corrected one-sided wonderful compactification. -/
theorem serreII_of_oddDegreePointDescent
    {Class Extension : Type*}
    (base : Extension)
    (OddDegree : Extension → Prop)
    (hasPoint neutral : Class → Extension → Prop)
    (oddSplitting : ∀ ξ, ∃ L, OddDegree L ∧ neutral ξ L)
    (point_iff_neutral : ∀ ξ L, hasPoint ξ L ↔ neutral ξ L)
    (oddPointDescent :
      ∀ ξ L, OddDegree L → hasPoint ξ L → hasPoint ξ base) :
    ∀ ξ, neutral ξ base := by
  intro ξ
  obtain ⟨L, hOdd, hNeutral⟩ := oddSplitting ξ
  apply (point_iff_neutral ξ base).mp
  exact oddPointDescent ξ L hOdd
    ((point_iff_neutral ξ L).mpr hNeutral)

/-- The alternating group on five letters has order sixty. -/
theorem alternatingGroup_fin_five_card :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup, Fintype.card_fin]
  norm_num [Nat.factorial]

/-- The order of A5 has only the prime support allowed in Gille's printed
`2^a * 3^b * 5^c` extension-degree hypothesis. -/
theorem alternatingGroup_fin_five_card_prime_support :
    Fintype.card (alternatingGroup (Fin 5)) = 2 ^ 2 * 3 * 5 := by
  rw [alternatingGroup_fin_five_card]
  norm_num

/-- A5 is not solvable. Consequently, an induction that replaces an arbitrary
Galois extension of degree `2^a * 3^b * 5^c` by a tower of cyclic extensions
of prime degrees 2, 3, and 5 does not cover every group allowed by that degree
hypothesis. This is an obstruction to that proof reduction, not a
counterexample to the stated cohomological theorem. -/
theorem alternatingGroup_fin_five_not_solvable :
    ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  intro h
  let _ : Group.IsSolvable (alternatingGroup (Fin 5)) := h
  have hlt :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial
      (alternatingGroup (Fin 5))
  rw [commutator_alternatingGroup_eq_top (by simp)] at hlt
  exact lt_irrefl _ hlt

/-- **Completion target B.** Let Candidate select the nonabelian cocycles
arising in the E8 application. If a generating family of local restrictions
admits one common gauge for every candidate, then every candidate is a global
coboundary.

The common-gauge hypothesis is the nonempty total intersection of the local
trivialization cosets; pairwise intersections alone are not asserted to
suffice. -/
theorem serreII_of_compatibleLocalGauges
    {Γ : Type u} {G : Type v} {I : Type w}
    [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (Candidate : NonabelianCocycle Γ G → Prop)
    (H : I → Subgroup Γ) (hgen : (⨆ i, H i) = ⊤)
    (commonGauge :
      ∀ a, Candidate a → ∃ b, ∀ i, a.IsLocalGauge (H i) b) :
    ∀ a, Candidate a → a.IsCoboundary := by
  intro a ha
  obtain ⟨b, hb⟩ := commonGauge a ha
  refine ⟨b, ?_⟩
  apply eq_trivial_gauge_of_generating_family a b H hgen
  intro i σ hσ
  exact hb i σ hσ

/-- **Completion target C.** The diagonal restriction--corestriction value
attached to one toral class equals the original class whenever its total
degree is congruent to one modulo an annihilator. Hence, if that single
diagonal value maps to the neutral class, so does the original class.

No closure property of the neutral fiber is assumed: toClass is an arbitrary
function, not a homomorphism. This is the point that avoids treating the
nonabelian neutral fiber as a subgroup. -/
theorem serreII_of_diagonalKernelNorm
    {ι A X : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (neutral : X) (toClass : A → X)
    (s : Finset ι) (degree multiplicity : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    {a : A} {e q : ℕ}
    (he : e • a = 0)
    (hcoefficient :
      ∑ i ∈ s, multiplicity i * degree i = 1 + q * e)
    (hkernelNorm :
      toClass (∑ i ∈ s, multiplicity i • cor i (res i a)) = neutral) :
    toClass a = neutral := by
  have hcorestriction :
      (∑ i ∈ s, multiplicity i • cor i (res i a)) =
        (∑ i ∈ s, multiplicity i * degree i) • a := by
    calc
      (∑ i ∈ s, multiplicity i • cor i (res i a)) =
          ∑ i ∈ s, multiplicity i • (degree i • a) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hindex i a]
      _ = ∑ i ∈ s, (multiplicity i * degree i) • a := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [smul_smul]
      _ = (∑ i ∈ s, multiplicity i * degree i) • a :=
        Finset.sum_smul.symm
  have hmultiple :
      (∑ i ∈ s, multiplicity i * degree i) • a = a := by
    rw [hcoefficient, add_nsmul, one_nsmul, ← smul_smul,
      he, smul_zero, add_zero]
  rw [hcorestriction, hmultiple] at hkernelNorm
  exact hkernelNorm

/-- The finite-etale form of completion target C. The product algebra is
encoded by a finite family of component cohomology groups together with
nonnegative multiplicities. Componentwise membership in the local neutral
fibers and the finite-etale kernel-norm principle supply the single diagonal
hypothesis used by `serreII_of_diagonalKernelNorm`. -/
theorem serreII_of_finiteEtaleKernelNorm
    {ι A X : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (Y : ι → Type*)
    (neutral : X) (localNeutral : ∀ i, Y i)
    (toClass : A → X) (localClass : ∀ i, B i → Y i)
    (s : Finset ι) (degree multiplicity : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    {a : A} {e q : ℕ}
    (he : e • a = 0)
    (hcoefficient :
      ∑ i ∈ s, multiplicity i * degree i = 1 + q * e)
    (hrestrictedKernel :
      ∀ i ∈ s, localClass i (res i a) = localNeutral i)
    (finiteEtaleKernelNorm :
      ∀ x : ∀ i, B i,
        (∀ i ∈ s, localClass i (x i) = localNeutral i) →
        toClass (∑ i ∈ s, multiplicity i • cor i (x i)) = neutral) :
    toClass a = neutral := by
  apply serreII_of_diagonalKernelNorm B neutral toClass s degree multiplicity
    res cor hindex he hcoefficient
  apply finiteEtaleKernelNorm (fun i => res i a)
  exact hrestrictedKernel

/-- The reverse implication in Proposition 6.35 at one base field: if the
target pointed set is a subsingleton (the Serre-II conclusion), then every
finite-etale kernel-norm statement is automatic. -/
theorem finiteEtaleKernelNorm_of_subsingleton_target
    {ι A X : Type*} [AddCommGroup A] [Subsingleton X]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (Y : ι → Type*)
    (neutral : X) (localNeutral : ∀ i, Y i)
    (toClass : A → X) (localClass : ∀ i, B i → Y i)
    (s : Finset ι) (multiplicity : ι → ℕ)
    (cor : ∀ i, B i →+ A) :
    ∀ x : ∀ i, B i,
      (∀ i ∈ s, localClass i (x i) = localNeutral i) →
      toClass (∑ i ∈ s, multiplicity i • cor i (x i)) = neutral := by
  intro x hx
  exact Subsingleton.elim _ _

/-- The additive restriction--corestriction and Bezout data do not imply the
diagonal kernel-norm principle. In `ZMod 2`, identity restriction and
corestriction obey the degree-three formula, the chosen class is killed by
two, and its restriction lies in a constant local neutral fiber, while its
corestriction is nonneutral for the identity base classifier.

This is an abstract obstruction, not an E8 counterexample. -/
theorem zmodTwo_diagonalKernelNorm_counterexample :
    let A := ZMod 2
    let res : A →+ A := AddMonoidHom.id A
    let cor : A →+ A := AddMonoidHom.id A
    let localClass : A → Unit := fun _ => ()
    let toClass : A → A := id
    let a : A := 1
    (∀ x, cor (res x) = 3 • x) ∧
      2 • a = 0 ∧
      3 = 1 + 1 * 2 ∧
      localClass (res a) = () ∧
      toClass (cor (res a)) ≠ 0 := by
  dsimp
  constructor
  · intro x
    rw [show 3 = 1 + 2 by omega, add_nsmul, one_nsmul,
      CharTwo.two_nsmul, add_zero]
  constructor
  · exact CharTwo.two_nsmul 1
  constructor
  · norm_num
  constructor
  · rfl
  · norm_num

end RiemannResearch.E8
