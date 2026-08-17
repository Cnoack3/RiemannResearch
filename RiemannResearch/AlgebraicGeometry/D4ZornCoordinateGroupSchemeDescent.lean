/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineGroupScalarExtensionCoherence
import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateModuleDescent
import RiemannResearch.AlgebraicGeometry.FpqcH1HopfIso
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateGaloisSemilinearAlgebraEffectiveDescent

/-!
# D4 finite-Galois descent to an affine group scheme and fpqc H¹

The existing D4 theorem selects a descended `K`-module and identifies its
scalar extension with the split related-triple coordinate module. The algebra
descent files additionally descend the unit and multiplication maps.

This module isolates the exact final upgrade datum: a commutative Hopf
`K`-algebra whose underlying module is the selected descended module and
whose Hopf scalar extension is the split related-triple coordinate Hopf
algebra. From that datum we construct:

* the descended affine group scheme over `K`;
* an isomorphism from its pullback to `L` to the split related-triple group;
* the induced scalar-extension map on global fpqc Čech `H¹`; and
* preservation of the neutral class.

Thus no additional group-scheme or fpqc descent hypothesis remains after the
effective Hopf lift. Constructing that lift from the already descended unit
and multiplication maps is still a separate algebra/Hopf coherence step.

Source: user-provided D4 semilinear-triality descent program.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

universe u v

private abbrev AIntegral := RelatedTripleCoordinateRing.{0}

local instance relatedTripleCoordinateDescentCommRing :
    CommRing AIntegral :=
  inferInstance

local instance relatedTripleCoordinateDescentHopfAlgebra :
    HopfAlgebra ℤ AIntegral :=
  relatedTripleCoordinateHopfAlgebra

/-- The precise effective Hopf lift of the existing D4 descended module.

The first field identifies the underlying `K`-module with the module already
selected by finite-Galois Čech descent. The second field upgrades its scalar
extension from a linear isomorphism to an isomorphism of commutative Hopf
algebras with the split related-triple coordinate algebra. -/
structure RelatedTripleCoordinateGaloisHopfDescentData
    (K L B : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [CommRing B] [HopfAlgebra K B]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) where
  moduleIso :
    ModuleCat.of K B ≅
      relatedTripleCoordinateGaloisDescendedModule K L diagram
  baseChangeHopfIso :
    CommHopfAlgCat.of L (TensorProduct K L B) ≅
      CommHopfAlgCat.of L (RelatedTripleCoordinateScalarExtension L)

namespace RelatedTripleCoordinateGaloisHopfDescentData

variable {K L B : Type u} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]
variable [CommRing B] [HopfAlgebra K B]
variable {diagram : (L ≃ₐ[K] L) →* DiagramSymmetry}
variable (D : RelatedTripleCoordinateGaloisHopfDescentData K L B diagram)

/-- The affine group scheme over `K` represented by the descended Hopf
algebra. -/
def descendedAffineGroupScheme :
    Grp (Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of K))) :=
  affineGroupSchemeGroup K B

/-- Pullback of the descended affine group scheme to `L` is the split
related-triple affine group scheme. -/
def baseChangeGroupIso :
    affineGroupSchemePullbackGroup K L B ≅
      affineGroupSchemeGroup L (RelatedTripleCoordinateScalarExtension L) :=
  affineGroupBaseChangeGroupIso K L B ≪≫
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of L)).mapIso
      D.baseChangeHopfIso.op).symm

/-- The Hopf base-change isomorphism as an isomorphism of represented affine
group presheaves over `L`. -/
def baseChangePresheafIso :
    affineGroupPresheaf (CommRingCat.of L)
        (CommRingCat.of (TensorProduct K L B)) ≅
      affineGroupPresheaf (CommRingCat.of L)
        (CommRingCat.of (RelatedTripleCoordinateScalarExtension L)) :=
  (affineGroupPresheafIsoOfHopfIso L
    (TensorProduct K L B)
    (RelatedTripleCoordinateScalarExtension L)
    D.baseChangeHopfIso).symm

/-- The Hopf base-change isomorphism identifies the corresponding global fpqc
Čech `H¹` sets over `L`. -/
def baseChangeFpqcH1Equiv :
    FpqcH1.{u, v} (CommRingCat.of L)
        (CommRingCat.of (TensorProduct K L B)) ≃
      FpqcH1.{u, v} (CommRingCat.of L)
        (CommRingCat.of (RelatedTripleCoordinateScalarExtension L)) :=
  FpqcH1.equivOfPresheafIso D.baseChangePresheafIso

/-- Restriction of a torsor class from the descended group over `K` to the
split related-triple group over `L`. -/
def fpqcRestriction :
    FpqcH1.{u, v} (CommRingCat.of K) (CommRingCat.of B) →
      FpqcH1.{u, v} (CommRingCat.of L)
        (CommRingCat.of (RelatedTripleCoordinateScalarExtension L)) :=
  fun ξ =>
    D.baseChangeFpqcH1Equiv (FpqcH1.scalarExtension K L B ξ)

/-- The fpqc restriction map furnished by effective Hopf descent preserves the
neutral torsor class. -/
@[simp] theorem fpqcRestriction_neutral :
    D.fpqcRestriction
        (FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of B)) =
      FpqcH1.neutral (CommRingCat.of L)
        (CommRingCat.of (RelatedTripleCoordinateScalarExtension L)) := by
  simp [fpqcRestriction, baseChangeFpqcH1Equiv]

/-- Effective Hopf descent upgrades the D4 module theorem all the way to an
affine group scheme split by `L/K` and a neutral-preserving fpqc `H¹`
restriction map. -/
theorem groupScheme_fpqc
    (D' : RelatedTripleCoordinateGaloisHopfDescentData K L B diagram) :
    Nonempty
      (affineGroupSchemePullbackGroup K L B ≅
        affineGroupSchemeGroup L
          (RelatedTripleCoordinateScalarExtension L)) ∧
      ∃ res :
          FpqcH1.{u, v} (CommRingCat.of K) (CommRingCat.of B) →
            FpqcH1.{u, v} (CommRingCat.of L)
              (CommRingCat.of (RelatedTripleCoordinateScalarExtension L)),
        res (FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of B)) =
          FpqcH1.neutral (CommRingCat.of L)
            (CommRingCat.of (RelatedTripleCoordinateScalarExtension L)) := by
  exact ⟨⟨baseChangeGroupIso D'⟩,
    ⟨fpqcRestriction D', fpqcRestriction_neutral D'⟩⟩

end RelatedTripleCoordinateGaloisHopfDescentData

end

end RiemannResearch.AlgebraicGeometry
