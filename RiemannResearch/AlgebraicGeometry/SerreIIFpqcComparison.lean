/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcH1
import RiemannResearch.AlgebraicGeometry.SerreIIConjecture

/-!
# Exact fpqc reformulation of Serre II

This module isolates the precise comparison datum needed to transfer the
project's cover-level fpqc neutrality results to the actual continuous
Galois-cohomological statement `SerreII.Conjecture`.

The terminal equivalence is a conditional research reduction. Its sole
comparison hypothesis is explicit and pointed. Constructing that comparison
requires passage from the canonical finite-Galois fixed-cover equivalences to
continuous absolute-Galois `H¹`, together with finite-stage compatibility and
cofinality. The cover-level local-neutrality side is not assumed silently: it
is displayed as a proposition equivalent to full Serre II once the comparison
is supplied.
-/

namespace RiemannResearch.AlgebraicGeometry.SerreII

universe u v

noncomputable section

/-- A pointed comparison between continuous Galois `H¹` and global fpqc Čech
`H¹` for exactly the fields and groups selected by the Serre-II hypotheses. -/
structure GaloisFpqcH1Comparison
    (Base : BaseCondition.{u}) (Group : GroupCondition.{u}) where
  /-- The comparison equivalence for every selected field and group. -/
  equiv :
    ∀ (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A],
      Base K → Group K A →
        GaloisH1 K A ≃
          FpqcH1.{u, v} (CommRingCat.of K) (CommRingCat.of A)
  /-- The comparison preserves the distinguished neutral classes. -/
  map_neutral :
    ∀ (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A]
      (hK : Base K) (hG : Group K A),
      equiv K A hK hG (GaloisH1.neutral K A) =
        FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A)

/-- The full Serre-II vanishing statement expressed in global fpqc Čech
`H¹`. -/
def FpqcConjecture
    (Base : BaseCondition.{u}) (Group : GroupCondition.{u}) : Prop :=
  ∀ (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A],
    Base K → Group K A →
      Subsingleton
        (FpqcH1.{u, v} (CommRingCat.of K) (CommRingCat.of A))

/-- The cover-level form of fpqc Serre II: every Čech class becomes neutral
after a witnessed fpqc refinement. -/
def FpqcLocalNeutrality
    (Base : BaseCondition.{u}) (Group : GroupCondition.{u}) : Prop :=
  ∀ (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A],
    Base K → Group K A →
      ∀ (I : Type v) (U : FpqcCover (CommRingCat.of K) I)
        (ξ : FpqcCechH1 (CommRingCat.of K) (CommRingCat.of A) U),
        ∃ (J : Type v) (W : FpqcCover (CommRingCat.of K) J)
          (r : W.Refinement U),
          r.pullbackH1 ξ =
            FpqcCechH1.neutral
              (CommRingCat.of K) (CommRingCat.of A) W

/-- Global fpqc Serre-II vanishing is equivalent to the explicit
neutralizing-refinement condition. -/
theorem fpqcConjecture_iff_localNeutrality
    (Base : BaseCondition.{u}) (Group : GroupCondition.{u}) :
    FpqcConjecture.{u, v} Base Group ↔
      FpqcLocalNeutrality.{u, v} Base Group := by
  constructor
  · intro h K A _ _ _ hK hG
    exact
      (FpqcH1.subsingleton_iff_every_class_locally_neutral
        (CommRingCat.of K) (CommRingCat.of A)).mp
        (h K A hK hG)
  · intro h K A _ _ _ hK hG
    exact
      (FpqcH1.subsingleton_iff_every_class_locally_neutral
        (CommRingCat.of K) (CommRingCat.of A)).mpr
        (h K A hK hG)

/-- Under a pointed comparison, a Galois class is neutral exactly when its
global fpqc image is neutral. -/
theorem galoisClass_eq_neutral_iff_fpqcImage_eq_neutral
    (Base : BaseCondition.{u}) (Group : GroupCondition.{u})
    (D : GaloisFpqcH1Comparison.{u, v} Base Group)
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A]
    (hK : Base K) (hG : Group K A) (ξ : GaloisH1 K A) :
    ξ = GaloisH1.neutral K A ↔
      D.equiv K A hK hG ξ =
        FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A) := by
  constructor
  · intro hξ
    rw [hξ, D.map_neutral K A hK hG]
  · intro hξ
    apply (D.equiv K A hK hG).injective
    rw [D.map_neutral K A hK hG]
    exact hξ

/-- A pointed Galois/fpqc comparison transports the full Serre-II conjecture
exactly to global fpqc `H¹` vanishing. -/
theorem conjecture_iff_fpqcConjecture
    (Base : BaseCondition.{u}) (Group : GroupCondition.{u})
    (D : GaloisFpqcH1Comparison.{u, v} Base Group) :
    Conjecture Base Group ↔ FpqcConjecture.{u, v} Base Group := by
  constructor
  · intro h K A _ _ _ hK hG
    have hsub : Subsingleton (GaloisH1 K A) :=
      (conjecture_iff_subsingleton Base Group).mp h K A hK hG
    let e := D.equiv K A hK hG
    exact ⟨fun x y => e.symm.injective (hsub.allEq (e.symm x) (e.symm y))⟩
  · intro h
    apply (conjecture_iff_subsingleton Base Group).mpr
    intro K A _ _ _ hK hG
    have hsub :
        Subsingleton
          (FpqcH1.{u, v} (CommRingCat.of K) (CommRingCat.of A)) :=
      h K A hK hG
    let e := D.equiv K A hK hG
    exact ⟨fun x y => e.injective (hsub.allEq (e x) (e y))⟩

/-- Once the pointed global comparison is supplied, full Serre II is exactly
the statement that every fpqc Čech class becomes neutral after refinement. -/
theorem conjecture_iff_fpqcLocalNeutrality
    (Base : BaseCondition.{u}) (Group : GroupCondition.{u})
    (D : GaloisFpqcH1Comparison.{u, v} Base Group) :
    Conjecture Base Group ↔
      FpqcLocalNeutrality.{u, v} Base Group := by
  rw [conjecture_iff_fpqcConjecture Base Group D,
    fpqcConjecture_iff_localNeutrality Base Group]

/-- Cover-level fpqc neutrality proves the actual continuous-Galois Serre-II
statement once the pointed global comparison has been constructed. -/
theorem conjecture_of_fpqcLocalNeutrality
    (Base : BaseCondition.{u}) (Group : GroupCondition.{u})
    (D : GaloisFpqcH1Comparison.{u, v} Base Group)
    (h : FpqcLocalNeutrality.{u, v} Base Group) :
    Conjecture Base Group :=
  (conjecture_iff_fpqcLocalNeutrality Base Group D).mpr h

end

end RiemannResearch.AlgebraicGeometry.SerreII
