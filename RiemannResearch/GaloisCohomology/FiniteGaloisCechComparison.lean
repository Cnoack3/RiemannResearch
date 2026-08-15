/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.GaloisCechFaceCompatibility
import RiemannResearch.GaloisCohomology.GaloisCechComparison

/-!
# Canonical finite-Galois Čech comparison

This module packages the scheme/tensor face compatibilities and the
degree-zero gauge calculation into the comparison datum between fixed-cover
fpqc Čech H¹ and discrete nonabelian Galois H¹.
-/

namespace RiemannResearch.GaloisCohomology

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RiemannResearch.AlgebraicGeometry
open scoped TensorProduct

universe u

noncomputable section

/-- Gauge cohomology in the left-multiplied equation orientation produced by
the singleton-cover Čech relation. -/
theorem GaloisCechCocycle.cohomologous_iff_exists_gaugeEquation
    {Γ : Type u} {G : Type*} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (a b : GaloisCechCocycle Γ G) :
    a.Cohomologous b ↔
      ∃ g : G, ∀ σ, g * a σ = b σ * σ • g := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    intro σ
    rw [hc, GaloisCechCocycle.gauge_apply]
    simp [smul_inv', mul_assoc]
  · rintro ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    apply GaloisCechCocycle.ext
    intro σ
    rw [GaloisCechCocycle.gauge_apply, inv_inv, smul_inv']
    exact (eq_mul_inv_iff_mul_eq).2 (hg σ).symm

/-- Singleton-cover cocycle sections are the explicit affine tensor-coordinate
Čech cocycles. -/
def finiteGaloisSingletonAffineCocycleEquiv
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L] :
    SingletonCocycleSection
        (finiteGaloisAffineGroupPresheaf K A)
        (finiteGaloisCoverObject K L) ≃
      AffineGaloisCechCocycle K L A where
  toFun s :=
    { val := finiteGaloisDoubleOverlapSectionMulEquiv K L A s.val
      cocycle_condition := by
        have hright :=
          (singletonCocycleCondition_iff_rightAssociated
            (finiteGaloisAffineGroupPresheaf K A)
            (finiteGaloisCoverObject K L) s.val).mp
              s.cocycle_condition
        have h := congrArg
          (finiteGaloisTripleOverlapSectionMulEquiv K L A) hright
        simpa only [map_mul,
          finiteGaloisTripleFace01_section_compatibility,
          finiteGaloisTripleFace12_section_compatibility,
          finiteGaloisTripleFace02_section_compatibility] using h }
  invFun f :=
    { val := (finiteGaloisDoubleOverlapSectionMulEquiv K L A).symm f.val
      cocycle_condition :=
        (singletonCocycleCondition_iff_rightAssociated
          (finiteGaloisAffineGroupPresheaf K A)
          (finiteGaloisCoverObject K L) _).mpr (by
            apply (finiteGaloisTripleOverlapSectionMulEquiv K L A).injective
            simpa only [map_mul,
              finiteGaloisTripleFace01_section_compatibility,
              finiteGaloisTripleFace12_section_compatibility,
              finiteGaloisTripleFace02_section_compatibility,
              MulEquiv.apply_symm_apply] using f.cocycle_condition) }
  left_inv s := by
    apply SingletonCocycleSection.ext
    exact (finiteGaloisDoubleOverlapSectionMulEquiv K L A).symm_apply_apply s.val
  right_inv f := by
    apply AffineGaloisCechCocycle.ext
    exact (finiteGaloisDoubleOverlapSectionMulEquiv K L A).apply_symm_apply f.val

/-- Actual fixed-cover presheaf cocycles are equivalent to nonabelian Galois
cocycles. -/
def finiteGaloisFixedCoverCocycleEquiv
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L] :
    PresheafOfGroups.OneCocycle
        (finiteGaloisAffineGroupPresheaf K A)
        (fun _ : PUnit.{1} => finiteGaloisCoverObject K L) ≃
      GaloisCechCocycle (L ≃ₐ[K] L) (AffineGaloisPoint K L A) :=
  (singletonOneCocycleEquiv
      (finiteGaloisAffineGroupPresheaf K A)
      (finiteGaloisCoverObject K L)).trans
    ((finiteGaloisSingletonAffineCocycleEquiv K L A).trans
      (affineGaloisCechCocycleEquiv K L A))

@[simp] lemma finiteGaloisFixedCoverCocycleEquiv_apply
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L]
    (a : PresheafOfGroups.OneCocycle
      (finiteGaloisAffineGroupPresheaf K A)
      (fun _ : PUnit.{1} => finiteGaloisCoverObject K L))
    (σ : L ≃ₐ[K] L) :
    finiteGaloisFixedCoverCocycleEquiv K L A a σ =
      finiteGaloisDoubleOverlapGaloisMulEquiv K L A
        (singletonOneCochainSection
          (finiteGaloisAffineGroupPresheaf K A)
          (finiteGaloisCoverObject K L) a.toOneCochain) σ := by
  rfl

@[simp] lemma finiteGaloisDoubleOverlapGalois_fst_apply
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L]
    (g : (finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op (finiteGaloisCoverObject K L)))
    (σ : L ≃ₐ[K] L) :
    finiteGaloisDoubleOverlapGaloisMulEquiv K L A
      ((finiteGaloisAffineGroupPresheaf K A).map
        (prod.fst : finiteGaloisCoverObject K L ⨯ finiteGaloisCoverObject K L ⟶
          finiteGaloisCoverObject K L).op g) σ =
      finiteGaloisCoverSectionMulEquiv K L A g := by
  change galoisDoubleOverlapPointMulEquiv K L A
    (finiteGaloisDoubleOverlapSectionMulEquiv K L A
      ((finiteGaloisAffineGroupPresheaf K A).map
        (prod.fst : finiteGaloisCoverObject K L ⨯ finiteGaloisCoverObject K L ⟶
          finiteGaloisCoverObject K L).op g)) σ = _
  rw [finiteGaloisDoubleOverlap_fst_section_compatibility,
    galoisDoubleOverlap_includeLeft_point]

@[simp] lemma finiteGaloisDoubleOverlapGalois_snd_apply
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L]
    (g : (finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op (finiteGaloisCoverObject K L)))
    (σ : L ≃ₐ[K] L) :
    finiteGaloisDoubleOverlapGaloisMulEquiv K L A
      ((finiteGaloisAffineGroupPresheaf K A).map
        (prod.snd : finiteGaloisCoverObject K L ⨯ finiteGaloisCoverObject K L ⟶
          finiteGaloisCoverObject K L).op g) σ =
      σ • finiteGaloisCoverSectionMulEquiv K L A g := by
  change galoisDoubleOverlapPointMulEquiv K L A
    (finiteGaloisDoubleOverlapSectionMulEquiv K L A
      ((finiteGaloisAffineGroupPresheaf K A).map
        (prod.snd : finiteGaloisCoverObject K L ⨯ finiteGaloisCoverObject K L ⟶
          finiteGaloisCoverObject K L).op g)) σ = _
  rw [finiteGaloisDoubleOverlap_snd_section_compatibility,
    galoisDoubleOverlap_includeRight_point]

/-- A singleton zero-cochain equation transports pointwise to the standard
Galois gauge equation. -/
theorem finiteGaloisSingletonGaugeEquation
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L]
    (a b : PresheafOfGroups.OneCocycle
      (finiteGaloisAffineGroupPresheaf K A)
      (fun _ : PUnit.{1} => finiteGaloisCoverObject K L))
    (g : (finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op (finiteGaloisCoverObject K L)))
    (hg :
      (finiteGaloisAffineGroupPresheaf K A).map prod.fst.op g *
          singletonOneCochainSection
            (finiteGaloisAffineGroupPresheaf K A)
            (finiteGaloisCoverObject K L) a.toOneCochain =
        singletonOneCochainSection
            (finiteGaloisAffineGroupPresheaf K A)
            (finiteGaloisCoverObject K L) b.toOneCochain *
          (finiteGaloisAffineGroupPresheaf K A).map prod.snd.op g)
    (σ : L ≃ₐ[K] L) :
    finiteGaloisCoverSectionMulEquiv K L A g *
        finiteGaloisFixedCoverCocycleEquiv K L A a σ =
      finiteGaloisFixedCoverCocycleEquiv K L A b σ *
        σ • finiteGaloisCoverSectionMulEquiv K L A g := by
  have hσ := congrFun
    (congrArg (finiteGaloisDoubleOverlapGaloisMulEquiv K L A) hg) σ
  rw [map_mul] at hσ
  rw [Pi.mul_apply] at hσ
  rw [finiteGaloisDoubleOverlapGalois_fst_apply] at hσ
  rw [map_mul] at hσ
  rw [Pi.mul_apply] at hσ
  rw [finiteGaloisDoubleOverlapGalois_snd_apply] at hσ
  rw [finiteGaloisFixedCoverCocycleEquiv_apply,
    finiteGaloisFixedCoverCocycleEquiv_apply]
  exact hσ

/-- Conversely, a pointwise Galois gauge equation transports back to the
universal singleton-cover zero-cochain equation. -/
theorem finiteGaloisSingletonEquationOfGaugeEquation
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L]
    (a b : PresheafOfGroups.OneCocycle
      (finiteGaloisAffineGroupPresheaf K A)
      (fun _ : PUnit.{1} => finiteGaloisCoverObject K L))
    (g : (finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op (finiteGaloisCoverObject K L)))
    (h : ∀ σ : L ≃ₐ[K] L,
      finiteGaloisCoverSectionMulEquiv K L A g *
          finiteGaloisFixedCoverCocycleEquiv K L A a σ =
        finiteGaloisFixedCoverCocycleEquiv K L A b σ *
          σ • finiteGaloisCoverSectionMulEquiv K L A g) :
    (finiteGaloisAffineGroupPresheaf K A).map prod.fst.op g *
          singletonOneCochainSection
            (finiteGaloisAffineGroupPresheaf K A)
            (finiteGaloisCoverObject K L) a.toOneCochain =
        singletonOneCochainSection
            (finiteGaloisAffineGroupPresheaf K A)
            (finiteGaloisCoverObject K L) b.toOneCochain *
          (finiteGaloisAffineGroupPresheaf K A).map prod.snd.op g := by
  apply (finiteGaloisDoubleOverlapGaloisMulEquiv K L A).injective
  funext σ
  rw [map_mul]
  rw [Pi.mul_apply]
  rw [finiteGaloisDoubleOverlapGalois_fst_apply]
  rw [map_mul]
  rw [Pi.mul_apply]
  rw [finiteGaloisDoubleOverlapGalois_snd_apply]
  rw [← finiteGaloisFixedCoverCocycleEquiv_apply,
    ← finiteGaloisFixedCoverCocycleEquiv_apply]
  exact h σ

/-- The canonical cocycle equivalence preserves and reflects the respective
zero-cochain relations. -/
theorem finiteGaloisFixedCoverCohomologous_iff
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L]
    (a b : PresheafOfGroups.OneCocycle
      (finiteGaloisAffineGroupPresheaf K A)
      (fun _ : PUnit.{1} => finiteGaloisCoverObject K L)) :
    a.IsCohomologous b ↔
      (finiteGaloisFixedCoverCocycleEquiv K L A a).Cohomologous
        (finiteGaloisFixedCoverCocycleEquiv K L A b) := by
  rw [singleton_isCohomologous_iff,
    GaloisCechCocycle.cohomologous_iff_exists_gaugeEquation]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨finiteGaloisCoverSectionMulEquiv K L A g, ?_⟩
    exact fun σ => finiteGaloisSingletonGaugeEquation K L A a b g hg σ
  · rintro ⟨g, hg⟩
    refine ⟨(finiteGaloisCoverSectionMulEquiv K L A).symm g, ?_⟩
    apply finiteGaloisSingletonEquationOfGaugeEquation K L A
    intro σ
    simpa using hg σ

/-- The canonical finite-Galois fixed-cover comparison datum. -/
def finiteGaloisFpqcGaloisCechComparison
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L] :
    RiemannResearch.AlgebraicGeometry.FpqcGaloisCechComparison
      (CommRingCat.of K) (CommRingCat.of A)
      (finiteGaloisFpqcCover K L)
      (L ≃ₐ[K] L) (AffineGaloisPoint K L A) where
  cocycleEquiv := finiteGaloisFixedCoverCocycleEquiv K L A
  cohomologous_iff := finiteGaloisFixedCoverCohomologous_iff K L A

/-- The canonical fixed-cover fpqc Čech H¹ equivalence with discrete
nonabelian Galois H¹. -/
def finiteGaloisCanonicalH1EquivNonabelian
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L] :
    FpqcCechH1 (CommRingCat.of K) (CommRingCat.of A)
        (finiteGaloisFpqcCover K L) ≃
      NonabelianH1 (L ≃ₐ[K] L) (AffineGaloisPoint K L A) :=
  RiemannResearch.AlgebraicGeometry.finiteGaloisH1EquivNonabelian
    K L (CommRingCat.of A) (AffineGaloisPoint K L A)
      (finiteGaloisFpqcGaloisCechComparison K L A)

end

end RiemannResearch.GaloisCohomology
