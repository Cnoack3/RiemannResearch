/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcCover
import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Common refinements of fpqc covers

Two witnessed fpqc covering families of an affine scheme have a witnessed
common refinement whose objects are their pairwise fiber products. The
construction uses Mathlib's intersection of zero-hypercovers for the fpqc
precoverage.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
open CategoryTheory.Limits

universe u v w

noncomputable section

namespace FpqcCover

/-- A witnessed fpqc cover, regarded as a zero-hypercover for the fpqc
precoverage. -/
def toZeroHypercover {R : CommRingCat.{u}} {I : Type v}
    (U : FpqcCover R I) :
    _root_.AlgebraicGeometry.Scheme.fpqcPrecoverage.ZeroHypercover
      (_root_.AlgebraicGeometry.Spec R) where
  toPreZeroHypercover :=
    { I₀ := I
      X := fun i => (U.obj i).left
      f := fun i => (U.obj i).hom }
  mem₀ := U.mem_fpqc

/-- The intersection zero-hypercover of two witnessed fpqc covers. Mathlib
constructs its objects as the pairwise fiber products of covering objects. -/
def commonZeroHypercover {R : CommRingCat.{u}}
    {I : Type v} {J : Type w}
    (U : FpqcCover R I) (V : FpqcCover R J) :
    _root_.AlgebraicGeometry.Scheme.fpqcPrecoverage.ZeroHypercover
      (_root_.AlgebraicGeometry.Spec R) :=
  U.toZeroHypercover.inter V.toZeroHypercover

/-- The witnessed common fpqc refinement of two covers. -/
def commonRefinement {R : CommRingCat.{u}}
    {I : Type v} {J : Type w}
    (U : FpqcCover R I) (V : FpqcCover R J) :
    FpqcCover R (commonZeroHypercover U V).I₀ where
  obj := fun k => Over.mk ((commonZeroHypercover U V).f k)
  mem_fpqc := (commonZeroHypercover U V).mem₀

/-- Each object of the common refinement is the corresponding pairwise fiber
product over `Spec R`. -/
theorem commonRefinement_obj_left {R : CommRingCat.{u}}
    {I : Type v} {J : Type w}
    (U : FpqcCover R I) (V : FpqcCover R J)
    (k : (commonZeroHypercover U V).I₀) :
    ((commonRefinement U V).obj k).left =
      pullback ((U.obj k.1).hom) ((V.obj k.2).hom) := by
  exact
    PreZeroHypercover.inter_X U.toZeroHypercover.toPreZeroHypercover
      V.toZeroHypercover.toPreZeroHypercover k

/-- The structure map of a common-refinement object is the first pullback
projection followed by the structure map of the left covering object. -/
theorem commonRefinement_obj_hom {R : CommRingCat.{u}}
    {I : Type v} {J : Type w}
    (U : FpqcCover R I) (V : FpqcCover R J)
    (k : (commonZeroHypercover U V).I₀) :
    ((commonRefinement U V).obj k).hom =
      pullback.fst ((U.obj k.1).hom) ((V.obj k.2).hom) ≫
        (U.obj k.1).hom := by
  exact
    PreZeroHypercover.inter_f U.toZeroHypercover.toPreZeroHypercover
      V.toZeroHypercover.toPreZeroHypercover k

/-- The common cover refines the left input cover. -/
def commonRefinementToLeft {R : CommRingCat.{u}}
    {I : Type v} {J : Type w}
    (U : FpqcCover R I) (V : FpqcCover R J) :
    (commonRefinement U V).Refinement U where
  index :=
    (U.toZeroHypercover.toPreZeroHypercover.interFst
      V.toZeroHypercover.toPreZeroHypercover).s₀
  hom := fun k =>
    Over.homMk
      ((U.toZeroHypercover.toPreZeroHypercover.interFst
        V.toZeroHypercover.toPreZeroHypercover).h₀ k)
      ((U.toZeroHypercover.toPreZeroHypercover.interFst
        V.toZeroHypercover.toPreZeroHypercover).w₀ k)

/-- The common cover refines the right input cover. -/
def commonRefinementToRight {R : CommRingCat.{u}}
    {I : Type v} {J : Type w}
    (U : FpqcCover R I) (V : FpqcCover R J) :
    (commonRefinement U V).Refinement V where
  index :=
    (U.toZeroHypercover.toPreZeroHypercover.interSnd
      V.toZeroHypercover.toPreZeroHypercover).s₀
  hom := fun k =>
    Over.homMk
      ((U.toZeroHypercover.toPreZeroHypercover.interSnd
        V.toZeroHypercover.toPreZeroHypercover).h₀ k)
      ((U.toZeroHypercover.toPreZeroHypercover.interSnd
        V.toZeroHypercover.toPreZeroHypercover).w₀ k)

/-- Data witnessing a common refinement of two fpqc covers. -/
structure CommonRefinementData {R : CommRingCat.{u}}
    {I : Type v} {J : Type w}
    (U : FpqcCover R I) (V : FpqcCover R J) where
  /-- Index type of the common refinement. -/
  K : Type (max v w)
  /-- The common fpqc cover. -/
  cover : FpqcCover R K
  /-- Its refinement map to the left cover. -/
  toLeft : cover.Refinement U
  /-- Its refinement map to the right cover. -/
  toRight : cover.Refinement V

/-- Any two witnessed fpqc covers of `Spec R` have a witnessed common
refinement by pairwise fiber products. -/
def commonRefinementData {R : CommRingCat.{u}}
    {I : Type v} {J : Type w}
    (U : FpqcCover R I) (V : FpqcCover R J) :
    CommonRefinementData U V where
  K := (commonZeroHypercover U V).I₀
  cover := commonRefinement U V
  toLeft := commonRefinementToLeft U V
  toRight := commonRefinementToRight U V

end FpqcCover

end

end RiemannResearch.AlgebraicGeometry
