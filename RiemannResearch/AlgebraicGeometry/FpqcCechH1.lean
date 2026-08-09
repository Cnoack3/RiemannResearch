/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.AlgebraicGeometry.Group.Affine
import RiemannResearch.AlgebraicGeometry.FpqcCechPullback

/-!
# Fixed-cover fpqc nonabelian Čech H¹

Nonabelian Čech H¹ of an affine group scheme on one indexed fpqc cover.
Cover infrastructure and generic refinement pullback live in focused modules.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u v w

noncomputable section

/-- The presheaf of groups represented by the affine group scheme
`Spec A → Spec R` associated to a Hopf algebra `A` over `R`. -/
abbrev affineGroupPresheaf (R A : CommRingCat.{u}) [HopfAlgebra R A] :
    (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat :=
  yonedaGrpObj
    ((_root_.AlgebraicGeometry.Spec A).asOver
      (_root_.AlgebraicGeometry.Spec R))

/-- Nonabelian Čech `H¹` of the affine group scheme `Spec A → Spec R` on
the fixed fpqc cover `U`. -/
abbrev FpqcCechH1 (R A : CommRingCat.{u}) [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover R I) : Type _ :=
  PresheafOfGroups.H1 (affineGroupPresheaf R A) U.obj

namespace FpqcCechH1

variable (R A : CommRingCat.{u}) [HopfAlgebra R A]
variable {I : Type v} (U : FpqcCover R I)

/-- The distinguished neutral class, represented by the trivial
nonabelian one-cocycle. -/
def neutral : FpqcCechH1 R A U :=
  1

/-- The explicit neutral class is the distinguished `One` element supplied by
Mathlib's fixed-cover `H¹`. -/
@[simp] theorem neutral_eq_one :
    neutral R A U = (1 : FpqcCechH1 R A U) :=
  rfl

/-- The neutral class is represented by the trivial one-cocycle. -/
theorem neutral_eq_trivialCocycleClass :
    neutral R A U =
      PresheafOfGroups.OneCocycle.class
        (1 : PresheafOfGroups.OneCocycle
          (affineGroupPresheaf R A) U.obj) :=
  rfl

/-- Neutrality of a fixed-cover cohomology class. -/
def IsNeutral (ξ : FpqcCechH1 R A U) : Prop :=
  ξ = neutral R A U

/-- The distinguished class is neutral. -/
@[simp] theorem isNeutral_neutral :
    IsNeutral R A U (neutral R A U) :=
  rfl

/-- Refinement pullback for the fixed-cover cohomology of an affine group
scheme. -/
def pullback {J : Type w} {V : FpqcCover R J}
    (r : V.Refinement U) :
    FpqcCechH1 R A U → FpqcCechH1 R A V :=
  r.pullbackH1

/-- Refinement pullback preserves the explicit neutral class. -/
@[simp] theorem pullback_neutral {J : Type w} {V : FpqcCover R J}
    (r : V.Refinement U) :
    pullback R A U r (neutral R A U) = neutral R A V :=
  r.pullbackH1_one

/-- A neutral fixed-cover class remains neutral after refinement. -/
theorem IsNeutral.pullback {J : Type w} {V : FpqcCover R J}
    {ξ : FpqcCechH1 R A U} (hξ : IsNeutral R A U ξ)
    (r : V.Refinement U) :
    IsNeutral R A V (pullback R A U r ξ) := by
  rw [IsNeutral] at hξ ⊢
  rw [hξ, pullback_neutral]

end FpqcCechH1

end

end RiemannResearch.AlgebraicGeometry
