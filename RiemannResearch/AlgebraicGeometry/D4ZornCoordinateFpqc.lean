/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4FpqcTriality
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateTriality

/-!
# fpqc triality for the represented split-Zorn related-triple group

The integral finite-equation related-triple functor is represented by its
coordinate Hopf algebra. Its faithful coordinate S₃ diagram-triality action
acts faithfully on the represented affine-group presheaf and induces actions
on fixed-cover and common-refinement Čech fpqc H1.

This module makes no identification with split Spin(8), and its FpqcH1
target is the common-refinement Čech quotient supplied by the project, not a
separate theorem classifying fpqc torsors.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

universe v w

noncomputable section

private abbrev A := RelatedTripleCoordinateRing.{0}

/-- The represented split-Zorn related-triple affine group equipped with its
faithful coordinate S₃ diagram-triality action. -/
noncomputable def relatedTripleCoordinateAffineGroupTrialityData :
    AffineGroupTrialityData
      (CommRingCat.of ℤ) (CommRingCat.of A) :=
  AffineGroupTrialityData.ofFaithfulHopfAction
    (R := CommRingCat.of ℤ)
    (A := CommRingCat.of A)
    relatedTripleCoordinateOuterHopfAction
    relatedTripleCoordinateOuterHopfAction_injective

/-- The faithful coordinate S₃ diagram-triality action on the affine group
presheaf represented by the split-Zorn related-triple coordinate Hopf algebra. -/
noncomputable def relatedTripleCoordinateAffineGroupTrialityAction :
    DiagramSymmetry →*
      CategoryTheory.Aut
        (affineGroupPresheaf
          (CommRingCat.of ℤ) (CommRingCat.of A)) :=
  relatedTripleCoordinateAffineGroupTrialityData.action

/-- The represented affine-group triality action remains faithful. -/
theorem relatedTripleCoordinateAffineGroupTrialityAction_injective :
    Function.Injective
      relatedTripleCoordinateAffineGroupTrialityAction :=
  relatedTripleCoordinateAffineGroupTrialityData.faithful

/-- Diagram-triality S₃ acts on fixed-cover Čech fpqc H1 of the represented split-Zorn
related-triple group. -/
def relatedTripleCoordinateFixedCoverFpqcH1Action
    {I : Type v} (U : FpqcCover (CommRingCat.of ℤ) I) :
    DiagramSymmetry →*
      Equiv.Perm
        (FpqcCechH1
          (CommRingCat.of ℤ) (CommRingCat.of A) U) :=
  relatedTripleCoordinateAffineGroupTrialityData.fixedCoverAction U

/-- The fixed-cover action preserves the neutral Čech class. -/
@[simp] theorem
    relatedTripleCoordinateFixedCoverFpqcH1Action_neutral
    {I : Type v} (U : FpqcCover (CommRingCat.of ℤ) I)
    (σ : DiagramSymmetry) :
    relatedTripleCoordinateFixedCoverFpqcH1Action U σ
        (FpqcCechH1.neutral
          (CommRingCat.of ℤ) (CommRingCat.of A) U) =
      FpqcCechH1.neutral
        (CommRingCat.of ℤ) (CommRingCat.of A) U :=
  relatedTripleCoordinateAffineGroupTrialityData
    |>.fixedCoverAction_neutral U σ

/-- The fixed-cover action commutes with every refinement pullback. -/
theorem relatedTripleCoordinateFixedCoverFpqcH1Action_pullback
    {I : Type v} {J : Type w}
    {U : FpqcCover (CommRingCat.of ℤ) I}
    {V : FpqcCover (CommRingCat.of ℤ) J}
    (r : V.Refinement U) (σ : DiagramSymmetry)
    (ξ : FpqcCechH1
      (CommRingCat.of ℤ) (CommRingCat.of A) U) :
    relatedTripleCoordinateFixedCoverFpqcH1Action V σ
        (r.pullbackH1 ξ) =
      r.pullbackH1
        (relatedTripleCoordinateFixedCoverFpqcH1Action U σ ξ) :=
  relatedTripleCoordinateAffineGroupTrialityData
    |>.fixedCoverAction_pullback r σ ξ

/-- Diagram-triality S₃ acts on the common-refinement Čech fpqc H1 quotient of the
represented split-Zorn related-triple group. -/
def relatedTripleCoordinateGlobalFpqcH1Action :
    DiagramSymmetry →*
      Equiv.Perm
        (FpqcH1.{0, v}
          (CommRingCat.of ℤ) (CommRingCat.of A)) :=
  relatedTripleCoordinateAffineGroupTrialityData.globalAction

/-- The global common-refinement action preserves the neutral class. -/
@[simp] theorem relatedTripleCoordinateGlobalFpqcH1Action_neutral
    (σ : DiagramSymmetry) :
    relatedTripleCoordinateGlobalFpqcH1Action.{v} σ
        (FpqcH1.neutral
          (CommRingCat.of ℤ) (CommRingCat.of A)) =
      FpqcH1.neutral
        (CommRingCat.of ℤ) (CommRingCat.of A) :=
  relatedTripleCoordinateAffineGroupTrialityData
    |>.globalAction_neutral σ

end

end RiemannResearch.AlgebraicGeometry
