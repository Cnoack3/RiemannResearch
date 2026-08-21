/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.ContinuousFiniteStageFpqcGauge
import RiemannResearch.AlgebraicGeometry.SerreIIFpqcComparison

/-!
# Continuous Galois/fpqc H¹ comparison boundary

The forward, neutral-preserving map from continuous Galois `H¹` to global
fpqc Čech `H¹` is unconditional. This module packages the two precise
remaining properties—finite-Galois representability and finite-Galois
detection of equality—and shows that they assemble the exact comparison
required by the Serre-II fpqc reformulation.

No inhabitant of the effectivity structure is asserted here. Constructing one
requires the still-missing effective fpqc torsor descent/classification and
finite-Galois cofinality results.
-/

namespace RiemannResearch.GaloisCohomology

open RiemannResearch.AlgebraicGeometry

universe u

noncomputable section

variable (K A : Type u) [Field K] [PerfectField K]
variable [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A]

/-- The exact cofinality/effectivity package needed to upgrade the constructed
continuous-Galois-to-fpqc map to an equivalence. -/
structure ContinuousGaloisFpqcH1Effectivity : Prop where
  /-- Every global fpqc Čech class is represented by a continuous Galois
  class, equivalently by one of its finite-Galois stages. -/
  finiteGalois_surjective :
    Function.Surjective (continuousGaloisToGlobalFpqcH1 K A)
  /-- Equality of global fpqc classes detects equality of the originating
  continuous Galois classes. -/
  finiteGalois_detects_equality :
    Function.Injective (continuousGaloisToGlobalFpqcH1 K A)

/-- The continuous Galois/fpqc equivalence produced by an effectivity
package. -/
noncomputable def continuousGaloisFpqcH1Equiv
    (D : ContinuousGaloisFpqcH1Effectivity K A) :
    AlgebraicGeometry.GaloisH1 K A ≃
      FpqcH1.{u, 0} (CommRingCat.of K) (CommRingCat.of A) :=
  Equiv.ofBijective (continuousGaloisToGlobalFpqcH1 K A)
    ⟨D.finiteGalois_detects_equality, D.finiteGalois_surjective⟩

/-- The effectivity-produced equivalence has the previously constructed
forward map as its underlying function. -/
@[simp] theorem continuousGaloisFpqcH1Equiv_apply
    (D : ContinuousGaloisFpqcH1Effectivity K A)
    (ξ : AlgebraicGeometry.GaloisH1 K A) :
    continuousGaloisFpqcH1Equiv K A D ξ =
      continuousGaloisToGlobalFpqcH1 K A ξ := rfl

/-- The effectivity-produced equivalence is pointed. -/
@[simp] theorem continuousGaloisFpqcH1Equiv_neutral
    (D : ContinuousGaloisFpqcH1Effectivity K A) :
    continuousGaloisFpqcH1Equiv K A D
        (AlgebraicGeometry.GaloisH1.neutral K A) =
      FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A) :=
  continuousGaloisToGlobalFpqcH1_neutral K A

end

end RiemannResearch.GaloisCohomology

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.GaloisCohomology

universe u

noncomputable section

/-- Assemble the exact Serre-II comparison from field/group hypotheses that
supply perfectness and finite type, together with the remaining
cofinality/effectivity package. -/
noncomputable def galoisFpqcH1ComparisonOfEffectivity
    (Base : BaseCondition.{u}) (Group : GroupCondition.{u})
    (hPerfect : ∀ (K : Type u) [Field K], Base K → PerfectField K)
    (hFiniteType :
      ∀ (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A],
        Group K A → Algebra.FiniteType K A)
    (D :
      ∀ (K A : Type u) [Field K] [PerfectField K]
        [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A],
        Base K → Group K A → ContinuousGaloisFpqcH1Effectivity K A) :
    GaloisFpqcH1Comparison.{u, 0} Base Group where
  equiv := fun K A _ _ _ hK hG => by
    let : PerfectField K := hPerfect K hK
    let : Algebra.FiniteType K A := hFiniteType K A hG
    exact continuousGaloisFpqcH1Equiv K A (D K A hK hG)
  map_neutral := by
    intro K A _ _ _ hK hG
    let : PerfectField K := hPerfect K hK
    let : Algebra.FiniteType K A := hFiniteType K A hG
    exact continuousGaloisFpqcH1Equiv_neutral K A (D K A hK hG)

end

end RiemannResearch.AlgebraicGeometry.SerreII
