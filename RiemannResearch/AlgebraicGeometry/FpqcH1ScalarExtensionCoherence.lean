/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcH1CanonicalScalarExtension
import RiemannResearch.AlgebraicGeometry.HopfFpqcH1Action

/-!
# Coherence for canonical scalar extension on fpqc H¹

This module proves the formal identity, composition, and associativity laws
for change-of-base data, identifies the tensor-coordinate unit and
associativity isomorphisms, and constructs the comparison refinements between
once-, twice-, and trivially base-changed fpqc covers.

The final two theorems reduce the normalized global identity and composition
laws to explicit fixed-cover coherence squares.  Those hypotheses precisely
record compatibility of the chosen pullback adjunction, `pullbackSpecIso'`,
and tensor-coordinate comparison; no quotient or tensor-algebra obligation
remains hidden in them.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Over
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Coefficient change on global H¹ -/

/-- Change coefficients without changing the base or the chosen cover. -/
def fpqcH1CoefficientChangeOfBaseData
    {R A B : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B) :
    FpqcH1ChangeOfBaseData.{u, v} R A R B where
  mapCover U := U
  mapRefinement r := r
  mapH1 _ ξ := PresheafH1.map η ξ
  mapH1_pullback r ξ := r.map_pullbackH1 η ξ
  mapH1_neutral U := PresheafH1.map_one (U := U.obj) η

/-- A morphism of coefficient presheaves induces a map on global fpqc H¹. -/
def FpqcH1.mapCoefficients
    {R A B : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B) :
    FpqcH1.{u, v} R A → FpqcH1.{u, v} R B :=
  (fpqcH1CoefficientChangeOfBaseData η :
    FpqcH1ChangeOfBaseData.{u, v} R A R B).toFun

@[simp] theorem FpqcH1.mapCoefficients_classOf
    {R A B : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B)
    {I : Type v} (U : FpqcCover R I)
    (ξ : FpqcCechH1 R A U) :
    FpqcH1.mapCoefficients η (FpqcH1.classOf R A U ξ) =
      FpqcH1.classOf R B U (PresheafH1.map η ξ) :=
  rfl

@[simp] theorem FpqcH1.mapCoefficients_neutral
    {R A B : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B) :
    FpqcH1.mapCoefficients.{u, v} η (FpqcH1.neutral R A) =
      FpqcH1.neutral R B :=
  (fpqcH1CoefficientChangeOfBaseData η :
    FpqcH1ChangeOfBaseData.{u, v} R A R B).toFun_neutral

@[simp] theorem FpqcH1.mapCoefficients_id
    {R A : CommRingCat.{u}} [HopfAlgebra R A] :
    FpqcH1.mapCoefficients.{u, v}
      (𝟙 (affineGroupPresheaf R A)) = id := by
  funext x
  refine Quotient.inductionOn x ?_
  intro a
  change FpqcH1.classOf R A a.cover
      (PresheafH1.map (𝟙 (affineGroupPresheaf R A)) a.value) =
    FpqcH1.classOf R A a.cover a.value
  rw [PresheafH1.map_id]
  rfl

theorem FpqcH1.mapCoefficients_comp
    {R A B C : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B] [HopfAlgebra R C]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B)
    (θ : affineGroupPresheaf R B ⟶ affineGroupPresheaf R C) :
    FpqcH1.mapCoefficients.{u, v} (η ≫ θ) =
      FpqcH1.mapCoefficients θ ∘ FpqcH1.mapCoefficients η := by
  funext x
  refine Quotient.inductionOn x ?_
  intro a
  change FpqcH1.classOf R C a.cover
      (PresheafH1.map (η ≫ θ) a.value) =
    FpqcH1.classOf R C a.cover
      (PresheafH1.map θ (PresheafH1.map η a.value))
  rw [PresheafH1.map_comp]
  rfl

/-! ## Iterated scalar extension and cover coherence -/

/-- The change-of-base datum for two successive scalar extensions. -/
def fpqcH1IteratedScalarExtensionChangeOfBaseData
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [HopfAlgebra R A] :
    FpqcH1ChangeOfBaseData.{u, v}
      (CommRingCat.of R) (CommRingCat.of A)
      (CommRingCat.of T)
      (CommRingCat.of
        (TensorProduct S T (TensorProduct R S A))) :=
  (fpqcH1ScalarExtensionChangeOfBaseData
      S T (TensorProduct R S A)).comp
    (fpqcH1ScalarExtensionChangeOfBaseData R S A)

@[simp] theorem fpqcH1IteratedScalarExtension_mapCover
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) :
    (fpqcH1IteratedScalarExtensionChangeOfBaseData
      R S T A).mapCover U =
      (U.baseChangeAlong (scalarExtensionSpecMap R S)).baseChangeAlong
        (scalarExtensionSpecMap S T) :=
  rfl

@[simp] theorem fpqcH1IteratedScalarExtension_mapH1
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I)
    (ξ : FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U) :
    (fpqcH1IteratedScalarExtensionChangeOfBaseData
      R S T A).mapH1 U ξ =
      FpqcCechH1.scalarExtension S T (TensorProduct R S A)
        (U.baseChangeAlong (scalarExtensionSpecMap R S))
        (FpqcCechH1.scalarExtension R S A U ξ) :=
  rfl

@[simp] theorem fpqcH1IteratedScalarExtension_toFun
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [HopfAlgebra R A] :
    (fpqcH1IteratedScalarExtensionChangeOfBaseData R S T A :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of T)
        (CommRingCat.of
          (TensorProduct S T (TensorProduct R S A)))).toFun =
      FpqcH1.scalarExtension S T (TensorProduct R S A) ∘
        FpqcH1.scalarExtension R S A := by
  exact FpqcH1ChangeOfBaseData.comp_toFun_eq
    (fpqcH1ScalarExtensionChangeOfBaseData
      S T (TensorProduct R S A))
    (fpqcH1ScalarExtensionChangeOfBaseData R S A)

@[simp] theorem scalarExtensionSpecMap_self
    (R : Type u) [CommRing R] :
    scalarExtensionSpecMap R R =
      𝟙 (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  simp [scalarExtensionSpecMap]

@[simp] theorem scalarExtensionSpecMap_comp
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] :
    scalarExtensionSpecMap S T ≫ scalarExtensionSpecMap R S =
      scalarExtensionSpecMap R T := by
  simp [scalarExtensionSpecMap, IsScalarTower.algebraMap_eq R S T]

/-- The self-base-change cover is objectwise isomorphic to the original. -/
def FpqcCover.scalarExtensionSelfObjIso
    (R : Type u) [CommRing R]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) (i : I) :
    (U.baseChangeAlong (scalarExtensionSpecMap R R)).obj i ≅ U.obj i := by
  rw [scalarExtensionSpecMap_self]
  exact (Over.pullbackId).app (U.obj i)

/-- The self-base-change cover refines the original cover. -/
def FpqcCover.scalarExtensionSelfRefinement
    (R : Type u) [CommRing R]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) :
    (U.baseChangeAlong (scalarExtensionSpecMap R R)).Refinement U where
  index := id
  hom i := (U.scalarExtensionSelfObjIso R i).hom

/-- Objectwise comparison between twice-pulled and directly pulled covers. -/
def FpqcCover.baseChangeAlongCompObjIso
    {R S T : CommRingCat.{u}}
    (f : _root_.AlgebraicGeometry.Spec S ⟶
      _root_.AlgebraicGeometry.Spec R)
    (g : _root_.AlgebraicGeometry.Spec T ⟶
      _root_.AlgebraicGeometry.Spec S)
    {I : Type v} (U : FpqcCover R I) (i : I) :
    ((U.baseChangeAlong f).baseChangeAlong g).obj i ≅
      (U.baseChangeAlong (g ≫ f)).obj i :=
  (Over.pullbackComp g f).symm.app (U.obj i)

theorem FpqcCover.Refinement.baseChangeAlongCompObjIso_naturality
    {R S T : CommRingCat.{u}}
    (f : _root_.AlgebraicGeometry.Spec S ⟶
      _root_.AlgebraicGeometry.Spec R)
    (g : _root_.AlgebraicGeometry.Spec T ⟶
      _root_.AlgebraicGeometry.Spec S)
    {I : Type v} {J : Type w}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U) (j : J) :
    (Over.pullback g).map ((Over.pullback f).map (r.hom j)) ≫
        (U.baseChangeAlongCompObjIso f g (r.index j)).hom =
      (V.baseChangeAlongCompObjIso f g j).hom ≫
        (Over.pullback (g ≫ f)).map (r.hom j) :=
  (Over.pullbackComp g f).symm.hom.naturality (r.hom j)

/-- The twice scalar-extended cover is objectwise isomorphic to the directly
scalar-extended cover. -/
def FpqcCover.scalarExtensionCompObjIso
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) (i : I) :
    ((U.baseChangeAlong (scalarExtensionSpecMap R S)).baseChangeAlong
        (scalarExtensionSpecMap S T)).obj i ≅
      (U.baseChangeAlong (scalarExtensionSpecMap R T)).obj i := by
  rw [← scalarExtensionSpecMap_comp R S T]
  exact U.baseChangeAlongCompObjIso
    (scalarExtensionSpecMap R S)
    (scalarExtensionSpecMap S T) i

/-- The twice scalar-extended cover refines the directly scalar-extended
cover through the pullback-composition isomorphism. -/
def FpqcCover.scalarExtensionCompRefinement
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) :
    ((U.baseChangeAlong (scalarExtensionSpecMap R S)).baseChangeAlong
        (scalarExtensionSpecMap S T)).Refinement
      (U.baseChangeAlong (scalarExtensionSpecMap R T)) where
  index := id
  hom i := (U.scalarExtensionCompObjIso R S T i).hom

/-! ## Tensor-coordinate coherence -/

/-- A bialgebra equivalence as an isomorphism in commutative Hopf algebras. -/
def commHopfAlgIsoOfBialgEquiv
    {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    (e : A ≃ₐc[R] B) :
    CommHopfAlgCat.of R A ≅ CommHopfAlgCat.of R B where
  hom := CommHopfAlgCat.ofHom e.toBialgHom
  inv := CommHopfAlgCat.ofHom e.symm.toBialgHom
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x

/-- Associativity of scalar extension as a bialgebra equivalence. -/
def affineGroupScalarExtensionCompBialgEquiv
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    TensorProduct S T (TensorProduct R S A) ≃ₐc[T]
      TensorProduct R T A := by
  apply BialgEquiv.ofAlgEquiv
    (Algebra.TensorProduct.cancelBaseChange R S T T A)
  · ext x
    simp [Bialgebra.TensorProduct.counitAlgHom_def]
    rw [TensorProduct.smul_tmul']
    rw [Algebra.TensorProduct.rid_tmul]
    simp
  · ext x
    simp [Bialgebra.TensorProduct.comulAlgHom_def]
    generalize hz :
      CoalgebraStruct.comul (R := R) (A := A) x = z
    clear hz
    induction z using TensorProduct.induction_on with
    | zero =>
        simp only [TensorProduct.tmul_zero, map_zero]
    | tmul a b =>
        simp only [
          Algebra.TensorProduct.tensorTensorTensorComm_tmul,
          Algebra.TensorProduct.map_tmul]
        have ha :
            ((Algebra.TensorProduct.cancelBaseChange R S T T A :
              TensorProduct S T (TensorProduct R S A) →ₐ[T]
                TensorProduct R T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] a))) =
                (1 ⊗ₜ[R] a) := by
          change
            (Algebra.TensorProduct.cancelBaseChange R S T T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)) = (1 ⊗ₜ[R] a)
          simpa only [one_smul] using
            (Algebra.TensorProduct.cancelBaseChange_tmul
              R S T T A (1 : T) (1 : S) a)
        have hb :
            ((Algebra.TensorProduct.cancelBaseChange R S T T A :
              TensorProduct S T (TensorProduct R S A) →ₐ[T]
                TensorProduct R T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] b))) =
                (1 ⊗ₜ[R] b) := by
          change
            (Algebra.TensorProduct.cancelBaseChange R S T T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] b)) = (1 ⊗ₜ[R] b)
          simpa only [one_smul] using
            (Algebra.TensorProduct.cancelBaseChange_tmul
              R S T T A (1 : T) (1 : S) b)
        rw [ha, hb]
    | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- The tensor-unit isomorphism on represented affine group presheaves. -/
def affineGroupPresheafScalarExtensionSelfIso
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A] :
    affineGroupPresheaf (CommRingCat.of R)
        (CommRingCat.of (TensorProduct R R A)) ≅
      affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A) :=
  (affineGroupPresheafIsoOfHopfIso
    R (TensorProduct R R A) A
    (commHopfAlgIsoOfBialgEquiv
      (Bialgebra.TensorProduct.lid R A))).symm

/-- Tensor associativity on represented affine group presheaves. -/
def affineGroupPresheafScalarExtensionCompIso
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    affineGroupPresheaf (CommRingCat.of T)
        (CommRingCat.of
          (TensorProduct S T (TensorProduct R S A))) ≅
      affineGroupPresheaf (CommRingCat.of T)
        (CommRingCat.of (TensorProduct R T A)) :=
  (affineGroupPresheafIsoOfHopfIso
    T (TensorProduct S T (TensorProduct R S A))
      (TensorProduct R T A)
      (commHopfAlgIsoOfBialgEquiv
        (affineGroupScalarExtensionCompBialgEquiv R S T A))).symm

/-! ## Global normalized laws from fixed-cover coherence -/

/-- The normalized identity law on global fpqc H¹ follows from the explicit
fixed-cover compatibility square. -/
theorem FpqcH1.scalarExtension_self_of_fixedCover
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A]
    (h : ∀ {I : Type v}
      (U : FpqcCover (CommRingCat.of R) I)
      (ξ : FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U),
      PresheafH1.map
          (affineGroupPresheafScalarExtensionSelfIso R A).hom
          (FpqcCechH1.scalarExtension R R A U ξ) =
        (U.scalarExtensionSelfRefinement R).pullbackH1 ξ) :
    FpqcH1.mapCoefficients.{u, v}
        (affineGroupPresheafScalarExtensionSelfIso R A).hom ∘
      FpqcH1.scalarExtension R R A = id := by
  let D :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of R) (CommRingCat.of A) :=
    (fpqcH1CoefficientChangeOfBaseData
      (affineGroupPresheafScalarExtensionSelfIso R A).hom).comp
        (fpqcH1ScalarExtensionChangeOfBaseData R R A)
  let E :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of R) (CommRingCat.of A) :=
    FpqcH1ChangeOfBaseData.identity
      (CommRingCat.of R) (CommRingCat.of A)
  have hDE : D.toFun = E.toFun := by
    apply FpqcH1ChangeOfBaseData.toFun_eq_of_refinement D E
      (fun U => U.scalarExtensionSelfRefinement R)
    intro I U ξ
    exact h U ξ
  calc
    _ = D.toFun :=
      (FpqcH1ChangeOfBaseData.comp_toFun_eq
        (fpqcH1CoefficientChangeOfBaseData
          (affineGroupPresheafScalarExtensionSelfIso R A).hom)
        (fpqcH1ScalarExtensionChangeOfBaseData R R A)).symm
    _ = E.toFun := hDE
    _ = id :=
      FpqcH1ChangeOfBaseData.identity_toFun_eq
        (CommRingCat.of R) (CommRingCat.of A)

/-- The normalized composition law on global fpqc H¹ follows from the
explicit fixed-cover compatibility square. -/
theorem FpqcH1.scalarExtension_comp_of_fixedCover
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A]
    (h : ∀ {I : Type v}
      (U : FpqcCover (CommRingCat.of R) I)
      (ξ : FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U),
      PresheafH1.map
          (affineGroupPresheafScalarExtensionCompIso R S T A).hom
          (FpqcCechH1.scalarExtension S T (TensorProduct R S A)
            (U.baseChangeAlong (scalarExtensionSpecMap R S))
            (FpqcCechH1.scalarExtension R S A U ξ)) =
        (U.scalarExtensionCompRefinement R S T).pullbackH1
          (FpqcCechH1.scalarExtension R T A U ξ)) :
    FpqcH1.mapCoefficients.{u, v}
        (affineGroupPresheafScalarExtensionCompIso R S T A).hom ∘
      FpqcH1.scalarExtension S T (TensorProduct R S A) ∘
      FpqcH1.scalarExtension R S A =
        FpqcH1.scalarExtension R T A := by
  let D :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of T)
          (CommRingCat.of (TensorProduct R T A)) :=
    (fpqcH1CoefficientChangeOfBaseData
      (affineGroupPresheafScalarExtensionCompIso R S T A).hom).comp
        (fpqcH1IteratedScalarExtensionChangeOfBaseData R S T A)
  let E :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of T)
          (CommRingCat.of (TensorProduct R T A)) :=
    fpqcH1ScalarExtensionChangeOfBaseData R T A
  have hDE : D.toFun = E.toFun := by
    apply FpqcH1ChangeOfBaseData.toFun_eq_of_refinement D E
      (fun U => U.scalarExtensionCompRefinement R S T)
    intro I U ξ
    exact h U ξ
  calc
    _ = (fpqcH1CoefficientChangeOfBaseData
          (affineGroupPresheafScalarExtensionCompIso R S T A).hom).toFun ∘
        (fpqcH1IteratedScalarExtensionChangeOfBaseData R S T A).toFun := by
      change
        (fpqcH1CoefficientChangeOfBaseData
            (affineGroupPresheafScalarExtensionCompIso R S T A).hom).toFun ∘
          FpqcH1.scalarExtension S T (TensorProduct R S A) ∘
          FpqcH1.scalarExtension R S A =
        _
      rw [fpqcH1IteratedScalarExtension_toFun]
    _ = D.toFun :=
      (FpqcH1ChangeOfBaseData.comp_toFun_eq
        (fpqcH1CoefficientChangeOfBaseData
          (affineGroupPresheafScalarExtensionCompIso R S T A).hom)
        (fpqcH1IteratedScalarExtensionChangeOfBaseData R S T A)).symm
    _ = E.toFun := hDE
    _ = FpqcH1.scalarExtension R T A :=
      rfl

end

end RiemannResearch.AlgebraicGeometry
