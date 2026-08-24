/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisHopfEffectivity
import RiemannResearch.AlgebraicGeometry.SerreIIE8BinaryIcosahedralSynchronizedTriality

/-!
# Synchronized finite-Galois D4 pairs

This module joins two effective related-triple coordinate descents at the
finite diagram-action layer used by the D4-by-D4 model of E8.  Pointwise
synchronization of the two Galois diagram homomorphisms has two simultaneous
consequences:

* each coordinate twist descends to an affine group scheme with the
  neutral-preserving fpqc restriction supplied by effective Hopf descent;
* the paired diagram transition preserves the identity discriminant graph
  defining the E8 overlattice glue.

This is the precise common interface between the coordinate group-scheme
construction and the finite synchronized-triality certificate.  It does not
construct the E8 subgroup embeddings, a transporter basepoint, or the target
centralizer incidence needed by the binary-icosahedral torsor reduction.
-/

namespace RiemannResearch.AlgebraicGeometry

open RiemannResearch.GaloisCohomology
open RiemannResearch.E8.BinaryIcosahedralSubgroups
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
open RiemannResearch.AlgebraicGeometry.SerreII

noncomputable section

universe u v

private abbrev AIntegral := RelatedTripleCoordinateRing.{0}

local instance : CommRing AIntegral := inferInstance

local instance : HopfAlgebra ℤ AIntegral :=
  relatedTripleCoordinateHopfAlgebra

/-- A pair of effective finite-Galois D4 diagram twists whose triality
components are synchronized pointwise. -/
structure RelatedTripleCoordinateGaloisSynchronizedPairData
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] where
  leftDiagram : (L ≃ₐ[K] L) →* DiagramSymmetry
  rightDiagram : (L ≃ₐ[K] L) →* DiagramSymmetry
  synchronized :
    ∀ γ : L ≃ₐ[K] L, rightDiagram γ = leftDiagram γ

/-- The effective affine-group/fpqc conclusion for one finite-Galois D4
coordinate twist. -/
abbrev RelatedTripleCoordinateGaloisGroupSchemeFpqcConclusion
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) : Prop :=
  Nonempty
      (affineGroupSchemePullbackGroup K L
          (relatedTripleCoordinateGaloisDescendedCoordinateRing K L diagram) ≅
        affineGroupSchemeGroup L
          (RelatedTripleCoordinateScalarExtension L)) ∧
    ∃ res :
        FpqcH1.{u, v} (CommRingCat.of K)
            (CommRingCat.of
              (relatedTripleCoordinateGaloisDescendedCoordinateRing
                K L diagram)) →
          FpqcH1.{u, v} (CommRingCat.of L)
            (CommRingCat.of (RelatedTripleCoordinateScalarExtension L)),
      res
          (FpqcH1.neutral (CommRingCat.of K)
            (CommRingCat.of
              (relatedTripleCoordinateGaloisDescendedCoordinateRing
                K L diagram))) =
        FpqcH1.neutral (CommRingCat.of L)
          (CommRingCat.of (RelatedTripleCoordinateScalarExtension L))

namespace RelatedTripleCoordinateGaloisSynchronizedPairData

/-- Pointwise synchronization is exactly what is needed for every Galois
transition to preserve the diagonal D4-pair discriminant glue. -/
theorem preserves_identityGraph
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : RelatedTripleCoordinateGaloisSynchronizedPairData K L)
    (γ : L ≃ₐ[K] L) :
    ∀ q, q ∈ discriminantGraph 1 →
      pairDiscriminantAction
        (D.leftDiagram γ) (D.rightDiagram γ) q ∈
          discriminantGraph 1 :=
  (pairAction_preserves_identityGraph_iff_synchronized
    (D.leftDiagram γ) (D.rightDiagram γ)).2
    (D.synchronized γ)

/-- Both synchronized D4 coordinate twists descend effectively to affine
group schemes with neutral-preserving fpqc restriction, and their common
diagram transition preserves the E8 identity glue. -/
theorem groupScheme_fpqc_and_preserves_identityGraph
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : RelatedTripleCoordinateGaloisSynchronizedPairData K L) :
    RelatedTripleCoordinateGaloisGroupSchemeFpqcConclusion.{u, v}
        K L D.leftDiagram ∧
      RelatedTripleCoordinateGaloisGroupSchemeFpqcConclusion.{u, v}
        K L D.rightDiagram ∧
      ∀ γ : L ≃ₐ[K] L, ∀ q, q ∈ discriminantGraph 1 →
        pairDiscriminantAction
          (D.leftDiagram γ) (D.rightDiagram γ) q ∈
            discriminantGraph 1 := by
  refine ⟨relatedTripleCoordinateGalois_groupScheme_fpqc
      K L D.leftDiagram, ?_⟩
  refine ⟨relatedTripleCoordinateGalois_groupScheme_fpqc
      K L D.rightDiagram, ?_⟩
  exact D.preserves_identityGraph

end RelatedTripleCoordinateGaloisSynchronizedPairData

/-- The remaining comparison data that realizes synchronized finite-Galois D4
transitions inside an E8-oriented transporter.

The synchronization itself is inherited from the coordinate pair. The only
new geometric inputs are a transition-to-Galois map and the fixed-basepoint
and target-centralizer incidence used by the transporter factorization
theorem. -/
structure RelatedTripleCoordinateGaloisSynchronizedPairTransporterRealization
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : RelatedTripleCoordinateGaloisSynchronizedPairData K L)
    {G : Type u} [Group G] [MulDistribMulAction SL2F5 G]
    (S6 S5 : Subgroup G) (theta : S6 ≃* S5) where
  transitionGalois : G → (L ≃ₐ[K] L)
  fixedBasepoint : G
  fixedBasepoint_mem :
    fixedBasepoint ∈ orientedSubgroupTransporter S6 S5 theta
  targetCentralizer_fixedByTetrahedral :
    Set.centralizer (S5 : Set G) ⊆
      (fixedPointSubgroup (G := G) binaryTetrahedralSubgroup : Set G)
  fixedBasepoint_fixedByDihedral :
    NonabelianCocycle.IsFixedBy
      binaryDihedralSubgroup fixedBasepoint

namespace RelatedTripleCoordinateGaloisSynchronizedPairTransporterRealization

/-- A synchronized coordinate-pair transporter realization supplies exactly
the transition geometry used by the binary-icosahedral E8 reduction. -/
def toTransitionGeometry
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {D : RelatedTripleCoordinateGaloisSynchronizedPairData K L}
    {G : Type u} [Group G] [MulDistribMulAction SL2F5 G]
    {S6 S5 : Subgroup G} {theta : S6 ≃* S5}
    (R :
      RelatedTripleCoordinateGaloisSynchronizedPairTransporterRealization
        D S6 S5 theta) :
    SynchronizedD4PairTransitionGeometry S6 S5 theta where
  leftTriality y := D.leftDiagram (R.transitionGalois y)
  rightTriality y := D.rightDiagram (R.transitionGalois y)
  synchronized y _ := D.synchronized (R.transitionGalois y)
  fixedBasepoint := R.fixedBasepoint
  fixedBasepoint_mem := R.fixedBasepoint_mem
  targetCentralizer_fixedByTetrahedral :=
    R.targetCentralizer_fixedByTetrahedral
  fixedBasepoint_fixedByDihedral := R.fixedBasepoint_fixedByDihedral

/-- The coordinate Hopf descents, their synchronized E8 glue action, and the
transporter transition geometry coexist in one effective endpoint. -/
theorem groupScheme_fpqc_and_transitionGeometry
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {D : RelatedTripleCoordinateGaloisSynchronizedPairData K L}
    {G : Type u} [Group G] [MulDistribMulAction SL2F5 G]
    {S6 S5 : Subgroup G} {theta : S6 ≃* S5}
    (R :
      RelatedTripleCoordinateGaloisSynchronizedPairTransporterRealization
        D S6 S5 theta) :
    RelatedTripleCoordinateGaloisGroupSchemeFpqcConclusion.{u, v}
        K L D.leftDiagram ∧
      RelatedTripleCoordinateGaloisGroupSchemeFpqcConclusion.{u, v}
        K L D.rightDiagram ∧
      Nonempty (SynchronizedD4PairTransitionGeometry S6 S5 theta) := by
  refine ⟨relatedTripleCoordinateGalois_groupScheme_fpqc
      K L D.leftDiagram, ?_⟩
  exact ⟨relatedTripleCoordinateGalois_groupScheme_fpqc
      K L D.rightDiagram, ⟨R.toTransitionGeometry⟩⟩

end RelatedTripleCoordinateGaloisSynchronizedPairTransporterRealization

end

end RiemannResearch.AlgebraicGeometry
