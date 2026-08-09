/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Indexed fpqc covers and refinements

This module defines indexed fpqc covers of an affine base and morphisms of
covering families. It contains no cohomology construction.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u v w

noncomputable section

/-- An indexed family in `Over (Spec R)` whose underlying scheme morphisms
form a cover in Mathlib's fpqc precoverage. -/
structure FpqcCover (R : CommRingCat.{u}) (I : Type v) where
  /-- The covering objects, including their structure morphisms to `Spec R`. -/
  obj : I → Over (_root_.AlgebraicGeometry.Spec R)
  /-- The assertion that the underlying arrow family is fpqc-covering. -/
  mem_fpqc :
    Presieve.ofArrows (fun i => (obj i).left) (fun i => (obj i).hom) ∈
      _root_.AlgebraicGeometry.Scheme.fpqcPrecoverage.coverings
        (_root_.AlgebraicGeometry.Spec R)

namespace FpqcCover

/-- A flat, surjective, quasi-compact morphism to `Spec R`, regarded as a
singleton fpqc cover. -/
def singleton {R : CommRingCat.{u}}
    {X : _root_.AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ _root_.AlgebraicGeometry.Spec R)
    [_root_.AlgebraicGeometry.Flat f]
    [_root_.AlgebraicGeometry.Surjective f]
    [_root_.AlgebraicGeometry.QuasiCompact f] :
    FpqcCover R PUnit where
  obj := fun _ => Over.mk f
  mem_fpqc := by
    change
      Presieve.ofArrows (fun _ : PUnit => X) (fun _ => f) ∈
        _root_.AlgebraicGeometry.Scheme.fpqcPrecoverage.coverings
          (_root_.AlgebraicGeometry.Spec R)
    rw [Presieve.ofArrows_pUnit]
    exact _root_.AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage f

/-- A refinement of fpqc covering families. Each object of `V` maps over the
base to a selected object of `U`. -/
structure Refinement {R : CommRingCat.{u}} {I : Type v} {J : Type w}
    (V : FpqcCover R J) (U : FpqcCover R I) where
  /-- The selected old index for each refined covering object. -/
  index : J → I
  /-- The refining morphism over `Spec R`. -/
  hom : ∀ j, V.obj j ⟶ U.obj (index j)

end FpqcCover

end

end RiemannResearch.AlgebraicGeometry
