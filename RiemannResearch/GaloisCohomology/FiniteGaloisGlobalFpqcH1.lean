/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcH1
import RiemannResearch.GaloisCohomology.FiniteGaloisCechComparison

/-!
# Finite Galois classes in global fpqc H¹

This module composes the canonical finite-Galois fixed-cover comparison with
the inclusion of a fixed-cover Čech class into the global common-refinement
quotient. It supplies an unconditional pointed map from finite nonabelian
Galois `H¹` to global fpqc Čech `H¹` and identifies its neutral fiber with a
concrete neutralizing-refinement condition.

This is a finite-stage bridge. It does not identify continuous absolute
Galois `H¹` with global fpqc `H¹`: that requires finite-quotient factorization,
coefficient descent, and compatibility under enlarging finite Galois
extensions.
-/

namespace RiemannResearch.GaloisCohomology

open RiemannResearch.AlgebraicGeometry

universe u

noncomputable section

/-- Send a finite nonabelian Galois `H¹` class through the canonical
finite-Galois Čech comparison and then into global fpqc Čech `H¹`. -/
def finiteGaloisToGlobalFpqcH1
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L] :
    NonabelianH1 (L ≃ₐ[K] L) (AffineGaloisPoint K L A) →
      FpqcH1.{u, 0} (CommRingCat.of K) (CommRingCat.of A) :=
  fun ξ =>
    FpqcH1.classOf (CommRingCat.of K) (CommRingCat.of A)
      (finiteGaloisFpqcCover K L)
      ((finiteGaloisCanonicalH1EquivNonabelian K L A).symm ξ)

/-- The finite-stage map to global fpqc `H¹` preserves the neutral class. -/
@[simp] theorem finiteGaloisToGlobalFpqcH1_neutral
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L] :
    finiteGaloisToGlobalFpqcH1 K L A
      (NonabelianH1.neutral :
        NonabelianH1 (L ≃ₐ[K] L) (AffineGaloisPoint K L A)) =
      FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A) := by
  unfold finiteGaloisToGlobalFpqcH1
  rw [show
    (finiteGaloisCanonicalH1EquivNonabelian K L A).symm
      (NonabelianH1.neutral :
        NonabelianH1 (L ≃ₐ[K] L) (AffineGaloisPoint K L A)) =
      FpqcCechH1.neutral (CommRingCat.of K) (CommRingCat.of A)
        (finiteGaloisFpqcCover K L) by
    apply (finiteGaloisCanonicalH1EquivNonabelian K L A).injective
    rw [Equiv.apply_symm_apply]
    exact (finiteGaloisCanonicalH1EquivNonabelian_neutral K L A).symm]
  exact FpqcH1.classOf_neutral
    (CommRingCat.of K) (CommRingCat.of A)
    (finiteGaloisFpqcCover K L)

/-- A finite Galois class maps to the neutral global fpqc class exactly when
its canonical fixed-cover Čech representative becomes neutral after one
witnessed fpqc refinement. -/
theorem finiteGaloisToGlobalFpqcH1_eq_neutral_iff_exists_refinement
    (K L A : Type u)
    [Field K] [Field L] [Algebra K L]
    [CommRing A] [HopfAlgebra K A]
    [FiniteDimensional K L] [IsGalois K L]
    (ξ : NonabelianH1 (L ≃ₐ[K] L) (AffineGaloisPoint K L A)) :
    finiteGaloisToGlobalFpqcH1 K L A ξ =
        FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A) ↔
      ∃ (J : Type) (W : FpqcCover (CommRingCat.of K) J)
        (r : W.Refinement (finiteGaloisFpqcCover K L)),
        r.pullbackH1
            ((finiteGaloisCanonicalH1EquivNonabelian K L A).symm ξ) =
          FpqcCechH1.neutral
            (CommRingCat.of K) (CommRingCat.of A) W := by
  exact FpqcH1.classOf_eq_neutral_iff_exists_refinement
    (CommRingCat.of K) (CommRingCat.of A)
    (finiteGaloisFpqcCover K L)
    ((finiteGaloisCanonicalH1EquivNonabelian K L A).symm ξ)

end

end RiemannResearch.GaloisCohomology
