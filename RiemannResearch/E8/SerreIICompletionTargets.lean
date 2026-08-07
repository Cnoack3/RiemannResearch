/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.LocalGaugeTransporter
import RiemannResearch.GroupTheory.CoprimeRestriction

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

end RiemannResearch.E8
