/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcCoverCommonRefinement

/-!
# Global fpqc nonabelian Čech H¹

This module passes from the fixed-cover groups of
`RiemannResearch.AlgebraicGeometry.FpqcCechH1` to a global carrier. A
representative consists of a witnessed fpqc cover of `Spec R` and a class in
the nonabelian Čech `H¹` of that cover. Two representatives are identified
when their pullbacks agree on a witnessed common refinement.

The main point needed for transitivity is that two refinement maps with the
same source and target induce the same map on `H¹`. This follows directly
from the cocycle identity: its mixed evaluation gives an explicit
zero-cochain relating the two pulled-back cocycles.

The resulting quotient is formed separately in each fixed universe for cover
index types. It is a global Čech carrier across witnessed covers; this module
does not identify it with a type of fpqc torsors.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u v w x

noncomputable section

namespace FpqcCover.Refinement

variable {R : CommRingCat.{u}}
variable {I : Type v} {J : Type w} {K : Type x}
variable {U : FpqcCover R I} {V : FpqcCover R J}
variable {W : FpqcCover R K}

/-- The identity refinement of a witnessed fpqc cover. -/
def refl (U : FpqcCover R I) : U.Refinement U where
  index := id
  hom := fun _ => 𝟙 _

/-- Composition of refinements. -/
def comp (s : W.Refinement V) (r : V.Refinement U) :
    W.Refinement U where
  index k := r.index (s.index k)
  hom k := s.hom k ≫ r.hom (s.index k)

variable (r : V.Refinement U) (s : W.Refinement V)
variable {G : (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat}

/-- Pullback along the identity refinement is the identity on nonabelian
Čech `H¹`. -/
@[simp] theorem pullbackH1_refl
    (ξ : PresheafOfGroups.H1 G U.obj) :
    pullbackH1 (refl U) ξ = ξ := by
  refine Quot.inductionOn ξ ?_
  intro γ
  apply PresheafOfGroups.OneCocycle.IsCohomologous.class_eq
  refine ⟨fun _ => 1, ?_⟩
  intro i j T a b
  simp only [pullbackOneCocycle, pullbackOneCochain, refl,
    map_one, one_mul, mul_one, Category.comp_id]
  rfl

/-- Pullback on nonabelian Čech `H¹` is functorial under composition of
refinements. -/
theorem pullbackH1_comp
    (ξ : PresheafOfGroups.H1 G U.obj) :
    pullbackH1 s (pullbackH1 r ξ) =
      pullbackH1 (comp s r) ξ := by
  refine Quot.inductionOn ξ ?_
  intro γ
  apply PresheafOfGroups.OneCocycle.IsCohomologous.class_eq
  refine ⟨fun _ => 1, ?_⟩
  intro i j T a b
  simp only [pullbackOneCocycle, pullbackOneCochain, comp,
    map_one, one_mul, mul_one, Category.assoc]

/-- A zero-cochain comparing pullbacks of a cocycle along two refinement maps
with the same source and target covers. -/
def comparisonZeroCochain
    {K : Type w} {V : FpqcCover R K}
    (r s : V.Refinement U)
    (γ : PresheafOfGroups.OneCocycle G U.obj) :
    PresheafOfGroups.ZeroCochain G V.obj :=
  fun j => γ.ev (s.index j) (r.index j) (s.hom j) (r.hom j)

/-- Pulling a cocycle back along two refinement maps with the same source and
target covers gives cohomologous cocycles. -/
theorem pullbackOneCocycle_isCohomologous
    {K : Type w} {V : FpqcCover R K}
    (r s : V.Refinement U)
    (γ : PresheafOfGroups.OneCocycle G U.obj) :
    (pullbackOneCocycle r γ).IsCohomologous
      (pullbackOneCocycle s γ) := by
  refine ⟨comparisonZeroCochain r s γ, ?_⟩
  intro i j T a b
  change
    G.map a.op
          (γ.ev (s.index i) (r.index i) (s.hom i) (r.hom i)) *
        γ.ev (r.index i) (r.index j)
          (a ≫ r.hom i) (b ≫ r.hom j) =
      γ.ev (s.index i) (s.index j)
          (a ≫ s.hom i) (b ≫ s.hom j) *
        G.map b.op
          (γ.ev (s.index j) (r.index j) (s.hom j) (r.hom j))
  rw [γ.ev_precomp, γ.ev_precomp]
  rw [γ.ev_trans, γ.ev_trans]

/-- The map on nonabelian Čech `H¹` induced by a refinement depends only on
its source and target covers, not on the selected refinement map. -/
theorem pullbackH1_eq
    {K : Type w} {V : FpqcCover R K}
    (r s : V.Refinement U)
    (ξ : PresheafOfGroups.H1 G U.obj) :
    pullbackH1 r ξ = pullbackH1 s ξ := by
  refine Quot.inductionOn ξ ?_
  intro γ
  exact (pullbackOneCocycle_isCohomologous r s γ).class_eq

end FpqcCover.Refinement

/-- A class in fixed-cover fpqc Čech `H¹`, together with its witnessed
cover. -/
structure FpqcH1Representative
    (R A : CommRingCat.{u}) [HopfAlgebra R A] where
  /-- The index type of the witnessed cover. -/
  I : Type v
  /-- The witnessed fpqc cover. -/
  cover : FpqcCover R I
  /-- The fixed-cover Čech cohomology class. -/
  value : FpqcCechH1 R A cover

namespace FpqcH1Representative

variable (R A : CommRingCat.{u}) [HopfAlgebra R A]

/-- Two fixed-cover classes are equivalent if their pullbacks agree on some
witnessed common refinement. -/
def Equivalent (a b : FpqcH1Representative.{u, v} R A) : Prop :=
  ∃ (K : Type v) (W : FpqcCover R K)
    (ra : W.Refinement a.cover) (rb : W.Refinement b.cover),
    ra.pullbackH1 a.value = rb.pullbackH1 b.value

theorem equivalent_refl
    (a : FpqcH1Representative.{u, v} R A) :
    Equivalent R A a a := by
  exact ⟨a.I, a.cover, FpqcCover.Refinement.refl a.cover,
    FpqcCover.Refinement.refl a.cover, rfl⟩

theorem equivalent_symm
    {a b : FpqcH1Representative.{u, v} R A}
    (h : Equivalent R A a b) :
    Equivalent R A b a := by
  rcases h with ⟨K, W, ra, rb, hab⟩
  exact ⟨K, W, rb, ra, hab.symm⟩

/-- Equality after witnessed common refinement is transitive. -/
theorem equivalent_trans
    {a b c : FpqcH1Representative.{u, v} R A}
    (hab : Equivalent R A a b)
    (hbc : Equivalent R A b c) :
    Equivalent R A a c := by
  rcases hab with ⟨K₁, W₁, ra, rb₁, hab⟩
  rcases hbc with ⟨K₂, W₂, rb₂, rc, hbc⟩
  let D := FpqcCover.commonRefinementData W₁ W₂
  refine ⟨D.K, D.cover, D.toLeft.comp ra, D.toRight.comp rc, ?_⟩
  calc
    (D.toLeft.comp ra).pullbackH1 a.value =
        D.toLeft.pullbackH1 (ra.pullbackH1 a.value) :=
      (FpqcCover.Refinement.pullbackH1_comp ra D.toLeft a.value).symm
    _ = D.toLeft.pullbackH1 (rb₁.pullbackH1 b.value) :=
      congrArg D.toLeft.pullbackH1 hab
    _ = (D.toLeft.comp rb₁).pullbackH1 b.value :=
      FpqcCover.Refinement.pullbackH1_comp rb₁ D.toLeft b.value
    _ = (D.toRight.comp rb₂).pullbackH1 b.value :=
      FpqcCover.Refinement.pullbackH1_eq
        (D.toLeft.comp rb₁) (D.toRight.comp rb₂) b.value
    _ = D.toRight.pullbackH1 (rb₂.pullbackH1 b.value) :=
      (FpqcCover.Refinement.pullbackH1_comp rb₂ D.toRight b.value).symm
    _ = D.toRight.pullbackH1 (rc.pullbackH1 c.value) :=
      congrArg D.toRight.pullbackH1 hbc
    _ = (D.toRight.comp rc).pullbackH1 c.value :=
      FpqcCover.Refinement.pullbackH1_comp rc D.toRight c.value

/-- The common-refinement equivalence relation on fixed-cover classes. -/
def setoid : Setoid (FpqcH1Representative.{u, v} R A) where
  r := Equivalent R A
  iseqv :=
    { refl := equivalent_refl R A
      symm := fun h => equivalent_symm R A h
      trans := fun h₁ h₂ => equivalent_trans R A h₁ h₂ }

end FpqcH1Representative

/-- Global fpqc Čech `H¹` of an affine group scheme, obtained by quotienting
fixed-cover classes by equality after witnessed common refinement. -/
def FpqcH1 (R A : CommRingCat.{u}) [HopfAlgebra R A] : Type _ :=
  Quotient (FpqcH1Representative.setoid R A)

namespace FpqcH1

variable (R A : CommRingCat.{u}) [HopfAlgebra R A]

/-- Send a fixed-cover Čech class to global fpqc Čech `H¹`. -/
def classOf {I : Type v} (U : FpqcCover R I)
    (ξ : FpqcCechH1 R A U) : FpqcH1.{u, v} R A :=
  Quotient.mk (FpqcH1Representative.setoid R A)
    { I := I, cover := U, value := ξ }

/-- Two fixed-cover classes define the same global class exactly when their
pullbacks agree on a witnessed common refinement. -/
theorem classOf_eq_iff {I J : Type v}
    (U : FpqcCover R I) (V : FpqcCover R J)
    (ξ : FpqcCechH1 R A U) (η : FpqcCechH1 R A V) :
    classOf R A U ξ = classOf R A V η ↔
      ∃ (K : Type v) (W : FpqcCover R K)
        (r : W.Refinement U) (s : W.Refinement V),
        r.pullbackH1 ξ = s.pullbackH1 η := by
  exact Quotient.eq

/-- Passing to a refinement does not change the global fpqc Čech class. -/
theorem classOf_pullback {I : Type v} {J : Type v}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U) (ξ : FpqcCechH1 R A U) :
    classOf R A U ξ = classOf R A V (r.pullbackH1 ξ) := by
  apply Quotient.sound
  exact ⟨J, V, r, FpqcCover.Refinement.refl V,
    (FpqcCover.Refinement.pullbackH1_refl
      (r.pullbackH1 ξ)).symm⟩

/-- The identity morphism of `Spec R` gives a canonical singleton fpqc
cover. -/
def trivialCover : FpqcCover R PUnit :=
  FpqcCover.singleton (𝟙 (_root_.AlgebraicGeometry.Spec R))

/-- The distinguished neutral global fpqc Čech class. -/
def neutral : FpqcH1.{u, v} R A :=
  classOf R A (trivialCover R)
    (FpqcCechH1.neutral R A (trivialCover R))

/-- Every fixed-cover neutral class represents the global neutral class. -/
theorem classOf_neutral {I : Type v} (U : FpqcCover R I) :
    classOf R A U (FpqcCechH1.neutral R A U) = neutral R A := by
  apply Quotient.sound
  let D := FpqcCover.commonRefinementData U (trivialCover R)
  exact ⟨D.K, D.cover, D.toLeft, D.toRight, by
    rw [FpqcCechH1.neutral_eq_one, FpqcCechH1.neutral_eq_one,
      FpqcCover.Refinement.pullbackH1_one,
      FpqcCover.Refinement.pullbackH1_one]⟩

end FpqcH1

end

end RiemannResearch.AlgebraicGeometry
