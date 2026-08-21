/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Extension.Generators
import Mathlib.Topology.Algebra.OpenSubgroup
import RiemannResearch.AlgebraicGeometry.AlgebraicGroupGaloisH1

/-!
# Continuity of the absolute-Galois action on finite-type affine group points

This module identifies represented geometric points with coordinate algebra
maps \`A →ₐ[K] AlgebraicClosure K\`. A finite set of algebra generators then
shows that every coordinate point is defined over a finite intermediate field.
Its absolute-Galois stabilizer is therefore open, which proves continuity of
the action on the discrete geometric-point group.

Source for the finite-field-of-definition argument and the resulting
continuity of the Galois action: J.-P. Serre, *Galois Cohomology*, Chapter I,
§5. The formal proof uses Mathlib's Krull topology and affine \`Spec\`
fully-faithfulness.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

noncomputable section

/-- The absolute Galois group of a perfect field is compact in its Krull
topology. This explicit instance bridges Mathlib's Galois-group instance across
the project abbreviation `Field.absoluteGaloisGroup`. -/
instance absoluteGaloisGroupCompactSpace
    (K : Type u) [Field K] [PerfectField K] :
    CompactSpace (Field.absoluteGaloisGroup K) := by
  change CompactSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
  infer_instance

/-- The absolute Galois group of a perfect field is totally disconnected in
its Krull topology. -/
instance absoluteGaloisGroupTotallyDisconnectedSpace
    (K : Type u) [Field K] [PerfectField K] :
    TotallyDisconnectedSpace (Field.absoluteGaloisGroup K) := by
  change TotallyDisconnectedSpace
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
  infer_instance

/-- Coordinate-algebra presentation of an affine geometric point. -/
abbrev CoordinateGeometricPoint
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] : Type u :=
  A →ₐ[K] AlgebraicClosure K

section CoordinatePoints

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]

/-- The absolute-Galois action on coordinate geometric points. -/
def coordinateGaloisSmul
    (σ : Field.absoluteGaloisGroup K)
    (x : CoordinateGeometricPoint K A) :
    CoordinateGeometricPoint K A :=
  σ.toAlgHom.comp x

instance : SMul (Field.absoluteGaloisGroup K) (CoordinateGeometricPoint K A) :=
  ⟨coordinateGaloisSmul K A⟩

instance : MulAction (Field.absoluteGaloisGroup K) (CoordinateGeometricPoint K A) where
  one_smul x := by
    apply AlgHom.ext
    intro a
    rfl
  mul_smul σ τ x := by
    apply AlgHom.ext
    intro a
    rfl

/-- Coordinate points carry the discrete coefficient topology. -/
instance : TopologicalSpace (CoordinateGeometricPoint K A) := ⊥

instance : DiscreteTopology (CoordinateGeometricPoint K A) := ⟨rfl⟩

/-- A finite intermediate field containing every coordinate of a geometric
point. -/
structure CoordinatePointFieldOfDefinition
    (x : CoordinateGeometricPoint K A) where
  field : IntermediateField K (AlgebraicClosure K)
  finite : FiniteDimensional K field
  image_mem : ∀ a : A, x a ∈ field

/-- A geometric point of a finite-type affine scheme is defined over a finite
intermediate field of the algebraic closure. -/
theorem exists_coordinatePointFieldOfDefinition
    [Algebra.FiniteType K A]
    (x : CoordinateGeometricPoint K A) :
    Nonempty (CoordinatePointFieldOfDefinition K A x) := by
  obtain ⟨n, ⟨P⟩⟩ :=
    Algebra.FiniteType.iff_exists_generators.mp
      (inferInstance : Algebra.FiniteType K A)
  let S : Set (AlgebraicClosure K) :=
    Set.range (fun i : Fin n => x (P.val i))
  let L : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.adjoin K S
  let _ : Finite S := Set.finite_range (fun i : Fin n => x (P.val i))
  let _ : Algebra.IsIntegral K (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.isIntegral
  have hLfinite : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin
      (fun y _ => Algebra.IsIntegral.isIntegral y)
  have hgen : Algebra.adjoin K (Set.range P.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top (MvPolynomial.aeval P.val)).2
      (fun a => ⟨P.σ' a, P.aeval_val_σ' a⟩)
  have himage : ∀ a : A, x a ∈ L := by
    intro a
    let B : Subalgebra K A := L.toSubalgebra.comap x
    have hgenerators : Set.range P.val ⊆ B := by
      rintro _ ⟨i, rfl⟩
      change x (P.val i) ∈ L
      exact (IntermediateField.subset_adjoin K S) ⟨i, rfl⟩
    have htop : (⊤ : Subalgebra K A) ≤ B := by
      rw [← hgen]
      exact Algebra.adjoin_le hgenerators
    exact htop (show a ∈ (⊤ : Subalgebra K A) from trivial)
  exact ⟨⟨L, hLfinite, himage⟩⟩

/-- Stabilizer of a coordinate geometric point. -/
def coordinateStabilizer
    (x : CoordinateGeometricPoint K A) : Set (Field.absoluteGaloisGroup K) :=
  {σ | σ • x = x}

/-- Absolute-Galois elements fixing an intermediate field pointwise. -/
def coordinateFixingSet
    (L : IntermediateField K (AlgebraicClosure K)) :
    Set (Field.absoluteGaloisGroup K) :=
  {σ | ∀ y : AlgebraicClosure K, y ∈ L → σ.toAlgHom y = y}

theorem coordinate_fixingSet_subset_stabilizer
    {x : CoordinateGeometricPoint K A}
    (D : CoordinatePointFieldOfDefinition K A x) :
    coordinateFixingSet K D.field ⊆ coordinateStabilizer K A x := by
  intro σ hσ
  apply AlgHom.ext
  intro a
  exact hσ (x a) (D.image_mem a)

theorem coordinate_fixingSet_isOpen
    (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] :
    IsOpen (coordinateFixingSet K L) := by
  change IsOpen {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
    ∀ y : AlgebraicClosure K, y ∈ L → σ y = y}
  have heq :
      {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
        ∀ y : AlgebraicClosure K, y ∈ L → σ y = y} =
      (L.fixingSubgroup : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) := by
    ext σ
    exact (IntermediateField.mem_fixingSubgroup_iff L σ).symm
  rw [heq]
  exact IntermediateField.fixingSubgroup_isOpen L

/-- The stabilizer of a coordinate point of a finite-type affine scheme is
open in the absolute Galois group. -/
theorem coordinate_stabilizer_isOpen
    [Algebra.FiniteType K A]
    (x : CoordinateGeometricPoint K A) :
    IsOpen (coordinateStabilizer K A x) := by
  obtain ⟨D⟩ := exists_coordinatePointFieldOfDefinition K A x
  let _ : FiniteDimensional K D.field := D.finite
  have hfixOpen := coordinate_fixingSet_isOpen K D.field
  have hfixOne : (1 : Field.absoluteGaloisGroup K) ∈
      coordinateFixingSet K D.field := by
    intro y hy
    rfl
  have hnhds :
      coordinateStabilizer K A x ∈
        nhds (1 : Field.absoluteGaloisGroup K) :=
    Filter.mem_of_superset (hfixOpen.mem_nhds hfixOne)
      (coordinate_fixingSet_subset_stabilizer K A D)
  let hsubgroup : Subgroup (Field.absoluteGaloisGroup K) :=
    { carrier := coordinateStabilizer K A x
      one_mem' := one_smul _ _
      mul_mem' := by
        intro σ τ hσ hτ
        exact (mul_smul σ τ x).trans
          ((congrArg (fun z => σ • z) hτ).trans hσ)
      inv_mem' := by
        intro σ hσ
        change σ⁻¹ • x = x
        symm
        have h := congrArg (fun z => σ⁻¹ • z) hσ
        simpa only [inv_smul_smul] using h }
  exact Subgroup.isOpen_of_mem_nhds hsubgroup hnhds

theorem coordinate_orbitMap_continuous
    [Algebra.FiniteType K A]
    (x : CoordinateGeometricPoint K A) :
    Continuous (fun σ : Field.absoluteGaloisGroup K => σ • x) :=
  GaloisCohomology.continuous_orbitMap_of_stabilizer_isOpen x
    (coordinate_stabilizer_isOpen K A x)

instance [Algebra.FiniteType K A] :
    ContinuousSMul (Field.absoluteGaloisGroup K) (CoordinateGeometricPoint K A) := by
  constructor
  rw [continuous_prod_of_discrete_right]
  exact coordinate_orbitMap_continuous K A

end CoordinatePoints

private theorem spec_map_preimage
    {R S : CommRingCat}
    (f : _root_.AlgebraicGeometry.Spec S ⟶
      _root_.AlgebraicGeometry.Spec R) :
    _root_.AlgebraicGeometry.Spec.map
        (_root_.AlgebraicGeometry.Spec.preimage f) = f := by
  rw [← _root_.AlgebraicGeometry.Spec.homEquiv_symm_apply]
  exact _root_.AlgebraicGeometry.Spec.homEquiv.symm_apply_apply f

section RepresentedPoints

variable (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A]

/-- Extract the coordinate algebra map from a represented geometric point. -/
def geometricPointToCoordinate
    (x : AlgebraicGroupGeometricPoints K A) :
    CoordinateGeometricPoint K A where
  toRingHom :=
    CommRingCat.Hom.hom
      (_root_.AlgebraicGeometry.Spec.preimage x.left)
  commutes' k := by
    have hw := x.w
    change
      x.left ≫
          _root_.AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap K A)) =
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) at hw
    have hxmap :
        _root_.AlgebraicGeometry.Spec.map
            (_root_.AlgebraicGeometry.Spec.preimage x.left) =
          x.left := by
      exact spec_map_preimage x.left
    have hring :
        CommRingCat.ofHom (algebraMap K A) ≫
            _root_.AlgebraicGeometry.Spec.preimage x.left =
          CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
      apply _root_.AlgebraicGeometry.Spec.map_injective
      rw [_root_.AlgebraicGeometry.Spec.map_comp, hxmap]
      exact hw
    exact congrArg
      (fun f : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) =>
        CommRingCat.Hom.hom f k) hring

/-- Build a represented geometric point from its coordinate algebra map. -/
def coordinateToGeometricPoint
    (x : CoordinateGeometricPoint K A) :
    AlgebraicGroupGeometricPoints K A := by
  change geometricPointObject K ⟶
    ((_root_.AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of K)))
  refine Over.homMk
    (_root_.AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom x.toRingHom)) ?_
  change
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom x.toRingHom) ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap K A)) =
      _root_.AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  rw [← _root_.AlgebraicGeometry.Spec.map_comp]
  congr 1
  ext k
  exact x.commutes k

theorem geometricPointToCoordinate_coordinateToGeometricPoint
    (x : CoordinateGeometricPoint K A) :
    geometricPointToCoordinate K A (coordinateToGeometricPoint K A x) = x := by
  apply AlgHom.ext
  intro a
  change
    CommRingCat.Hom.hom
        (_root_.AlgebraicGeometry.Spec.preimage
          (_root_.AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom x.toRingHom))) a = x a
  rw [_root_.AlgebraicGeometry.Spec.preimage_map]
  rfl

theorem coordinateToGeometricPoint_geometricPointToCoordinate
    (x : AlgebraicGroupGeometricPoints K A) :
    coordinateToGeometricPoint K A (geometricPointToCoordinate K A x) = x := by
  apply CommaMorphism.ext
  · change
      _root_.AlgebraicGeometry.Spec.map
          (_root_.AlgebraicGeometry.Spec.preimage x.left) = x.left
    exact spec_map_preimage x.left
  · rfl

/-- Represented geometric points are equivalent to coordinate algebra maps. -/
def geometricPointCoordinateEquiv :
    AlgebraicGroupGeometricPoints K A ≃ CoordinateGeometricPoint K A where
  toFun := geometricPointToCoordinate K A
  invFun := coordinateToGeometricPoint K A
  left_inv := coordinateToGeometricPoint_geometricPointToCoordinate K A
  right_inv := geometricPointToCoordinate_coordinateToGeometricPoint K A

/-- The represented-point/coordinate-point equivalence is equivariant for the
absolute-Galois actions. -/
theorem geometricPointToCoordinate_smul
    (σ : Field.absoluteGaloisGroup K)
    (x : AlgebraicGroupGeometricPoints K A) :
    geometricPointToCoordinate K A (σ • x) =
      σ • geometricPointToCoordinate K A x := by
  apply AlgHom.ext
  intro a
  change
    CommRingCat.Hom.hom
        (_root_.AlgebraicGeometry.Spec.preimage (σ • x).left) a =
      σ.toAlgHom
        (CommRingCat.Hom.hom
          (_root_.AlgebraicGeometry.Spec.preimage x.left) a)
  have hleft :
      (σ • x).left =
        (absoluteGaloisPointEndomorphism K σ).left ≫ x.left := rfl
  rw [hleft]
  have hxmap :
      _root_.AlgebraicGeometry.Spec.map
          (_root_.AlgebraicGeometry.Spec.preimage x.left) =
        x.left := by
    exact spec_map_preimage x.left
  have hσmap :
      _root_.AlgebraicGeometry.Spec.map
          (_root_.AlgebraicGeometry.Spec.preimage
            (absoluteGaloisPointEndomorphism K σ).left) =
        (absoluteGaloisPointEndomorphism K σ).left := by
    exact spec_map_preimage (absoluteGaloisPointEndomorphism K σ).left
  have hcompmap :
      _root_.AlgebraicGeometry.Spec.map
          (_root_.AlgebraicGeometry.Spec.preimage
            ((absoluteGaloisPointEndomorphism K σ).left ≫ x.left)) =
        (absoluteGaloisPointEndomorphism K σ).left ≫ x.left := by
    exact spec_map_preimage
      ((absoluteGaloisPointEndomorphism K σ).left ≫ x.left)
  have hpre :
      _root_.AlgebraicGeometry.Spec.preimage
          ((absoluteGaloisPointEndomorphism K σ).left ≫ x.left) =
        _root_.AlgebraicGeometry.Spec.preimage x.left ≫
          _root_.AlgebraicGeometry.Spec.preimage
            (absoluteGaloisPointEndomorphism K σ).left := by
    apply _root_.AlgebraicGeometry.Spec.map_injective
    rw [_root_.AlgebraicGeometry.Spec.map_comp, hxmap, hσmap, hcompmap]
    rfl
  have hσpre :
      _root_.AlgebraicGeometry.Spec.preimage
          (absoluteGaloisPointEndomorphism K σ).left =
        CommRingCat.ofHom σ.toAlgHom.toRingHom := by
    apply _root_.AlgebraicGeometry.Spec.map_injective
    rw [hσmap]
    rfl
  have hprea := congrArg
    (fun f : CommRingCat.of A ⟶ CommRingCat.of (AlgebraicClosure K) =>
      CommRingCat.Hom.hom f a) hpre
  rw [hσpre] at hprea
  exact hprea

/-- The represented geometric-point group has the explicit discrete topology
used in continuous nonabelian Galois cohomology. -/
instance : DiscreteTopology (AlgebraicGroupGeometricPoints K A) := ⟨rfl⟩

/-- Stabilizer of a represented geometric point. -/
def geometricPointStabilizer
    (x : AlgebraicGroupGeometricPoints K A) :
    Set (Field.absoluteGaloisGroup K) :=
  {σ | σ • x = x}

/-- For a finite-type affine group, every represented geometric point has an
open absolute-Galois stabilizer. -/
theorem geometricPoint_stabilizer_isOpen
    [Algebra.FiniteType K A]
    (x : AlgebraicGroupGeometricPoints K A) :
    IsOpen (geometricPointStabilizer K A x) := by
  have heq :
      geometricPointStabilizer K A x =
        coordinateStabilizer K A (geometricPointToCoordinate K A x) := by
    ext σ
    constructor
    · intro hσ
      change σ • x = x at hσ
      change
        σ • geometricPointToCoordinate K A x =
          geometricPointToCoordinate K A x
      simpa only [geometricPointToCoordinate_smul] using
        congrArg (geometricPointToCoordinate K A) hσ
    · intro hσ
      change
        σ • geometricPointToCoordinate K A x =
          geometricPointToCoordinate K A x at hσ
      apply (geometricPointCoordinateEquiv K A).injective
      change geometricPointToCoordinate K A (σ • x) =
        geometricPointToCoordinate K A x
      rw [geometricPointToCoordinate_smul]
      exact hσ
  rw [heq]
  exact coordinate_stabilizer_isOpen K A (geometricPointToCoordinate K A x)

theorem geometricPoint_orbitMap_continuous
    [Algebra.FiniteType K A]
    (x : AlgebraicGroupGeometricPoints K A) :
    Continuous (fun σ : Field.absoluteGaloisGroup K => σ • x) :=
  GaloisCohomology.continuous_orbitMap_of_stabilizer_isOpen x
    (geometricPoint_stabilizer_isOpen K A x)

/-- The natural absolute-Galois action on the discrete geometric-point group
of a finite-type affine group is continuous. -/
instance [Algebra.FiniteType K A] :
    ContinuousSMul (Field.absoluteGaloisGroup K)
      (AlgebraicGroupGeometricPoints K A) := by
  constructor
  rw [continuous_prod_of_discrete_right]
  exact geometricPoint_orbitMap_continuous K A

end RepresentedPoints

namespace AbsoluteGaloisOpenNormalSubgroup

variable (K : Type u) [Field K] [PerfectField K]
variable (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K))

/-- An open subgroup of the absolute Galois group, regarded as a closed
subgroup for the infinite Galois correspondence. -/
def toClosedSubgroup :
    ClosedSubgroup (Field.absoluteGaloisGroup K) where
  toSubgroup := H
  isClosed' := H.toOpenSubgroup.isClosed

/-- The finite intermediate field cut out by an open normal subgroup of the
absolute Galois group. -/
abbrev fixedField : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField
    (H : Subgroup (Field.absoluteGaloisGroup K))

/-- Infinite Galois correspondence recovers the original open normal subgroup
from its fixed field. -/
theorem fixingSubgroup_fixedField :
    (fixedField K H).fixingSubgroup =
      (H : Subgroup (Field.absoluteGaloisGroup K)) := by
  exact InfiniteGalois.fixingSubgroup_fixedField (toClosedSubgroup K H)

/-- The field fixed by an open normal subgroup is finite over the perfect base
field. -/
theorem fixedField_finiteDimensional :
    FiniteDimensional K (fixedField K H) := by
  apply (InfiniteGalois.isOpen_iff_finite (fixedField K H)).mp
  rw [fixingSubgroup_fixedField K H]
  exact H.toOpenSubgroup.isOpen

/-- The field fixed by an open normal subgroup is Galois over the perfect base
field. -/
theorem fixedField_isGalois :
    IsGalois K (fixedField K H) := by
  apply (InfiniteGalois.normal_iff_isGalois (fixedField K H)).mp
  rw [fixingSubgroup_fixedField K H]
  exact H.isNormal'

/-- The finite quotient by an open normal subgroup is canonically the Galois
group of its fixed field. -/
def quotientEquivGaloisGroup :
    Field.absoluteGaloisGroup K ⧸
        (H : Subgroup (Field.absoluteGaloisGroup K)) ≃*
      ((fixedField K H) ≃ₐ[K] (fixedField K H)) := by
  have hnormal :
      ((toClosedSubgroup K H : ClosedSubgroup
        (Field.absoluteGaloisGroup K)) : Subgroup
          (Field.absoluteGaloisGroup K)).Normal := by
    change (H : Subgroup (Field.absoluteGaloisGroup K)).Normal
    exact H.isNormal'
  exact @InfiniteGalois.normalAutEquivQuotient
    K (AlgebraicClosure K) _ _ _ _ (toClosedSubgroup K H) hnormal

end AbsoluteGaloisOpenNormalSubgroup

namespace GaloisH1

open GaloisCohomology
open GaloisCohomology.ContinuousNonabelianH1

/-- Every class in the continuous Galois H¹ of a finite-type affine group over
a perfect field has a representative obtained by pullback of a genuine
finite-level cocycle with kernel-fixed coefficients. -/
theorem exists_representative_finiteStageCocycle
    (K A : Type u) [Field K] [PerfectField K]
    [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A]
    (ξ : GaloisH1 K A) :
    ∃ a : ContinuousNonabelianCocycle
        (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A),
      ContinuousNonabelianH1.classOf a = ξ ∧
        Nonempty
          (ContinuousNonabelianCocycle.ActionCompatibleFiniteQuotientFactorization
            a) := by
  exact exists_representative_actionCompatibleFiniteQuotientFactorization ξ

end GaloisH1

end

end RiemannResearch.AlgebraicGeometry
