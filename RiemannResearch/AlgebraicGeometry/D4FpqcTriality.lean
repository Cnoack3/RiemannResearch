/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcH1Functoriality
import RiemannResearch.LinearAlgebra.RootSystem.D4Triality

/-!
# Diagram triality on affine-group fpqc H1

A faithful action of the D4 diagram-symmetry group on a represented affine
group presheaf induces actions on fixed-cover and global common-refinement
nonabelian fpqc Cech H1. Both actions preserve the distinguished neutral
class, and the fixed-cover action commutes with every refinement pullback
through coefficient functoriality.

AffineGroupTrialityData is the precise representable-group bridge: its action
must come from the affine group under study. This file does not supply a
coordinate Hopf algebra for split Spin(8), nor identify the related-triples
point group with such a represented group scheme.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality

universe u v w

noncomputable section

/-- A faithful diagram-symmetry action on the presheaf represented by one
commutative Hopf algebra. -/
structure AffineGroupTrialityData
    (R A : CommRingCat.{u}) [HopfAlgebra R A] where
  action : DiagramSymmetry →*
    CategoryTheory.Aut (affineGroupPresheaf R A)
  faithful : Function.Injective action

namespace AffineGroupTrialityData

variable {R A : CommRingCat.{u}} [HopfAlgebra R A]
variable (D : AffineGroupTrialityData R A)

/-- Triality acts on nonabelian Cech H1 for every fixed fpqc cover. -/
def fixedCoverAction {I : Type v} (U : FpqcCover R I) :
    DiagramSymmetry →* Equiv.Perm (FpqcCechH1 R A U) where
  toFun σ := PresheafH1.equiv (D.action σ)
  map_one' := by
    apply Equiv.ext
    intro ξ
    change PresheafH1.map (D.action 1).hom ξ = ξ
    rw [D.action.map_one]
    exact congrFun PresheafH1.map_id ξ
  map_mul' σ τ := by
    apply Equiv.ext
    intro ξ
    change PresheafH1.map (D.action (σ * τ)).hom ξ =
      PresheafH1.map (D.action σ).hom
        (PresheafH1.map (D.action τ).hom ξ)
    rw [D.action.map_mul]
    exact congrFun
      (PresheafH1.map_comp (D.action τ).hom (D.action σ).hom) ξ

/-- Triality acts on the global common-refinement fpqc H1 quotient. -/
def globalAction :
    DiagramSymmetry →* Equiv.Perm (FpqcH1.{u, v} R A) where
  toFun σ := FpqcH1.equiv (D.action σ)
  map_one' := by
    apply Equiv.ext
    intro ξ
    change FpqcH1.map (D.action 1).hom ξ = ξ
    rw [D.action.map_one]
    exact congrFun FpqcH1.map_id ξ
  map_mul' σ τ := by
    apply Equiv.ext
    intro ξ
    change FpqcH1.map (D.action (σ * τ)).hom ξ =
      FpqcH1.map (D.action σ).hom
        (FpqcH1.map (D.action τ).hom ξ)
    rw [D.action.map_mul]
    exact congrFun
      (FpqcH1.map_comp (D.action τ).hom (D.action σ).hom) ξ

/-- The fixed-cover action preserves the neutral class. -/
@[simp] theorem fixedCoverAction_neutral {I : Type v}
    (U : FpqcCover R I) (σ : DiagramSymmetry) :
    D.fixedCoverAction U σ (FpqcCechH1.neutral R A U) =
      FpqcCechH1.neutral R A U := by
  change PresheafH1.map (D.action σ).hom 1 = 1
  exact PresheafH1.map_one _

/-- The global action preserves the neutral class. -/
@[simp] theorem globalAction_neutral (σ : DiagramSymmetry) :
    D.globalAction σ (FpqcH1.neutral R A) =
      FpqcH1.neutral R A :=
  FpqcH1.map_neutral _

/-- The fixed-cover triality action commutes with refinement pullback. -/
theorem fixedCoverAction_pullback
    {I : Type v} {J : Type w}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U) (σ : DiagramSymmetry)
    (ξ : FpqcCechH1 R A U) :
    D.fixedCoverAction V σ (r.pullbackH1 ξ) =
      r.pullbackH1 (D.fixedCoverAction U σ ξ) :=
  FpqcCover.Refinement.map_pullbackH1 r (D.action σ).hom ξ

end AffineGroupTrialityData

end

end RiemannResearch.AlgebraicGeometry
