/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FiniteGaloisFpqcCover
import RiemannResearch.AlgebraicGeometry.FpqcCechH1
import RiemannResearch.GaloisCohomology.PresheafGaloisCechComparison

/-!
# Affine fpqc and Galois Čech H¹ comparison

The cross-layer bridge specializing the generic presheaf comparison to affine
group schemes and singleton finite-Galois fpqc covers.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
open RiemannResearch.GaloisCohomology

universe u₁ v₁ w₁ x₁

noncomputable section

/-- The cocycle-level comparison datum specialized to an affine group scheme
on a fixed fpqc cover. The canonical finite-Galois affine instance is
constructed in `FiniteGaloisCechComparison`. -/
abbrev FpqcGaloisCechComparison
    (R A : CommRingCat.{u₁}) [HopfAlgebra R A]
    {I : Type v₁} (U : FpqcCover R I)
    (Γ : Type w₁) (G : Type x₁) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] :=
  PresheafGaloisCechComparison
    (affineGroupPresheaf R A) U.obj Γ G

namespace FpqcGaloisCechComparison

variable (R A : CommRingCat.{u₁}) [HopfAlgebra R A]
variable {I : Type v₁} (U : FpqcCover R I)
variable (Γ : Type w₁) (G : Type x₁) [Group Γ] [Group G]
variable [MulDistribMulAction Γ G]

/-- Once the affine fixed-cover cocycle comparison datum is supplied, it
descends without further hypotheses to an equivalence from fixed-cover fpqc
Čech H¹ to discrete nonabelian H¹. -/
def h1EquivNonabelian
    (D : FpqcGaloisCechComparison R A U Γ G) :
    FpqcCechH1 R A U ≃ NonabelianH1 Γ G :=
  PresheafGaloisCechComparison.h1EquivNonabelian D

end FpqcGaloisCechComparison

/-- For the singleton finite Galois fpqc cover, an explicit cocycle-level
Yoneda comparison datum yields the desired fixed-cover Čech/Galois H¹
equivalence. -/
def finiteGaloisH1EquivNonabelian
    (K L : Type u₁) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (A : CommRingCat.{u₁}) [HopfAlgebra (CommRingCat.of K) A]
    (G : Type x₁) [Group G]
    [MulDistribMulAction (L ≃ₐ[K] L) G]
    (D : FpqcGaloisCechComparison
      (CommRingCat.of K) A (finiteGaloisFpqcCover K L)
      (L ≃ₐ[K] L) G) :
    FpqcCechH1 (CommRingCat.of K) A
        (finiteGaloisFpqcCover K L) ≃
      NonabelianH1 (L ≃ₐ[K] L) G :=
  FpqcGaloisCechComparison.h1EquivNonabelian
    (CommRingCat.of K) A (finiteGaloisFpqcCover K L)
      (L ≃ₐ[K] L) G D

end

end RiemannResearch.AlgebraicGeometry
