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

/-- The represented geometric-point group is multiplicatively equivalent to
its coordinate-algebra presentation. This strengthens the plain coordinate
equivalence by recording compatibility with the Hopf-algebra group law. -/
def geometricPointCoordinateMulEquiv :
    AlgebraicGroupGeometricPoints K A ≃*
      WithConv (CoordinateGeometricPoint K A) := by
  change
    (((_root_.AlgebraicGeometry.Spec
        (CommRingCat.of (AlgebraicClosure K))).asOver
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of K))) ⟶
      ((_root_.AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of K)))) ≃*
      WithConv (A →ₐ[K] AlgebraicClosure K)
  exact _root_.AlgebraicGeometry.Spec.mapMulEquiv.symm

/-- The multiplicative coordinate equivalence has the same underlying
coordinate map as `geometricPointCoordinateEquiv`. -/
@[simp] theorem geometricPointCoordinateMulEquiv_apply
    (x : AlgebraicGroupGeometricPoints K A) :
    (geometricPointCoordinateMulEquiv K A x).ofConv =
      geometricPointToCoordinate K A x := by
  rfl

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

section FixedFieldPoints

variable (A : Type u) [CommRing A] [HopfAlgebra K A]

/-- Geometric points fixed by an open normal subgroup of the absolute Galois
group. -/
abbrev FixedGeometricPointGroup :=
  FixedPoints.subgroup H (AlgebraicGroupGeometricPoints K A)

/-- Include affine points over the fixed field into coordinate points over
the algebraic closure. -/
def fixedFieldCoordinateInclusion :
    WithConv (A →ₐ[K] fixedField K H) →*
      WithConv (A →ₐ[K] AlgebraicClosure K) where
  toFun f :=
    WithConv.toConv ((fixedField K H).val.comp f.ofConv)
  map_one' := by
    apply WithConv.ofConv_injective
    rfl
  map_mul' f g := by
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib (fixedField K H).val f g

/-- Include fixed-field affine points into represented geometric points. -/
def fixedFieldPointToGeometricPoint :
    WithConv (A →ₐ[K] fixedField K H) →*
      AlgebraicGroupGeometricPoints K A :=
  (geometricPointCoordinateMulEquiv K A).symm.toMonoidHom.comp
    (fixedFieldCoordinateInclusion K H A)

/-- Coordinate formula for the fixed-field inclusion. -/
@[simp] theorem geometricPointToCoordinate_fixedFieldPointToGeometricPoint
    (f : WithConv (A →ₐ[K] fixedField K H)) :
    geometricPointToCoordinate K A
        (fixedFieldPointToGeometricPoint K H A f) =
      (fixedField K H).val.comp f.ofConv := by
  change
    ((geometricPointCoordinateMulEquiv K A)
      ((geometricPointCoordinateMulEquiv K A).symm
        (fixedFieldCoordinateInclusion K H A f))).ofConv = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The multiplicative coordinate equivalence sends the represented
fixed-field point back to its included coordinate map. -/
@[simp] theorem geometricPointCoordinateMulEquiv_fixedFieldPointToGeometricPoint
    (f : WithConv (A →ₐ[K] fixedField K H)) :
    geometricPointCoordinateMulEquiv K A
        (fixedFieldPointToGeometricPoint K H A f) =
      fixedFieldCoordinateInclusion K H A f := by
  change
    (geometricPointCoordinateMulEquiv K A)
        ((geometricPointCoordinateMulEquiv K A).symm
          (fixedFieldCoordinateInclusion K H A f)) =
      fixedFieldCoordinateInclusion K H A f
  exact (geometricPointCoordinateMulEquiv K A).apply_symm_apply _

/-- A fixed-field affine point is fixed by the chosen open normal subgroup
after inclusion into the algebraic closure. -/
theorem fixedFieldPointToGeometricPoint_mem_fixed
    (f : WithConv (A →ₐ[K] fixedField K H)) :
    fixedFieldPointToGeometricPoint K H A f ∈
      FixedPoints.subgroup H (AlgebraicGroupGeometricPoints K A) := by
  apply (FixedPoints.mem_subgroup H _ _).2
  intro h
  apply (geometricPointCoordinateEquiv K A).injective
  change
    geometricPointToCoordinate K A
        (h.1 • fixedFieldPointToGeometricPoint K H A f) =
      geometricPointToCoordinate K A
        (fixedFieldPointToGeometricPoint K H A f)
  rw [geometricPointToCoordinate_smul,
    geometricPointToCoordinate_fixedFieldPointToGeometricPoint]
  apply AlgHom.ext
  intro x
  have hfix :=
    (IntermediateField.mem_fixedField_iff
      (H : Subgroup (Field.absoluteGaloisGroup K))
      ((fixedField K H).val (f.ofConv x))).mp (f.ofConv x).2
  exact hfix h.1 h.2

/-- The multiplicative inclusion of fixed-field points with its codomain
restricted to the subgroup of invariant geometric points. -/
def fixedFieldPointToFixedGeometricPoint :
    WithConv (A →ₐ[K] fixedField K H) →*
      FixedGeometricPointGroup K H A :=
  (fixedFieldPointToGeometricPoint K H A).codRestrict _
    (fixedFieldPointToGeometricPoint_mem_fixed K H A)

/-- Inclusion of fixed-field coordinate maps into algebraic-closure
coordinate maps is injective. -/
theorem fixedFieldCoordinateInclusion_injective :
    Function.Injective (fixedFieldCoordinateInclusion K H A) := by
  intro f g hfg
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  exact congrArg
    (fun q : WithConv (A →ₐ[K] AlgebraicClosure K) => q.ofConv x) hfg

/-- The fixed-field point inclusion is injective. -/
theorem fixedFieldPointToFixedGeometricPoint_injective :
    Function.Injective (fixedFieldPointToFixedGeometricPoint K H A) := by
  intro f g hfg
  apply fixedFieldCoordinateInclusion_injective K H A
  have hgeom := congrArg Subtype.val hfg
  change
    (geometricPointCoordinateMulEquiv K A).symm
        (fixedFieldCoordinateInclusion K H A f) =
      (geometricPointCoordinateMulEquiv K A).symm
        (fixedFieldCoordinateInclusion K H A g) at hgeom
  exact (geometricPointCoordinateMulEquiv K A).symm.injective hgeom

/-- Every invariant geometric point is defined over the fixed field. -/
theorem fixedFieldPointToFixedGeometricPoint_surjective :
    Function.Surjective (fixedFieldPointToFixedGeometricPoint K H A) := by
  intro x
  have hrange : ∀ y : A,
      (geometricPointCoordinateMulEquiv K A x.1).ofConv y ∈ fixedField K H := by
    intro y
    rw [IntermediateField.mem_fixedField_iff
      (H : Subgroup (Field.absoluteGaloisGroup K))]
    intro σ hσ
    let h : H := ⟨σ, hσ⟩
    have hxfix :=
      (FixedPoints.mem_subgroup H (AlgebraicGroupGeometricPoints K A) x.1).1
        x.2 h
    have hcoord := congrArg (geometricPointToCoordinate K A) hxfix
    change
      geometricPointToCoordinate K A (h.1 • x.1) =
        geometricPointToCoordinate K A x.1 at hcoord
    rw [geometricPointToCoordinate_smul] at hcoord
    exact congrArg (fun f : A →ₐ[K] AlgebraicClosure K => f y) hcoord
  let f : WithConv (A →ₐ[K] fixedField K H) :=
    WithConv.toConv
      (AlgHom.codRestrict
        (geometricPointCoordinateMulEquiv K A x.1).ofConv
        (fixedField K H).toSubalgebra hrange)
  refine ⟨f, ?_⟩
  apply Subtype.ext
  apply (geometricPointCoordinateMulEquiv K A).injective
  change
    geometricPointCoordinateMulEquiv K A
        (fixedFieldPointToGeometricPoint K H A f) =
      geometricPointCoordinateMulEquiv K A x.1
  rw [geometricPointCoordinateMulEquiv_fixedFieldPointToGeometricPoint]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro y
  rfl

/-- Affine points over the finite fixed field are multiplicatively equivalent
to the geometric points fixed by its absolute-Galois kernel. -/
def fixedFieldPointMulEquivFixedGeometricPoint :
    WithConv (A →ₐ[K] fixedField K H) ≃*
      FixedGeometricPointGroup K H A :=
  MulEquiv.ofBijective (fixedFieldPointToFixedGeometricPoint K H A)
    ⟨fixedFieldPointToFixedGeometricPoint_injective K H A,
      fixedFieldPointToFixedGeometricPoint_surjective K H A⟩

/-- The orientation used to transport kernel-fixed cocycle coefficients to
finite-field affine points. -/
def fixedGeometricPointMulEquivFixedFieldPoint :
    FixedGeometricPointGroup K H A ≃*
      WithConv (A →ₐ[K] fixedField K H) :=
  (fixedFieldPointMulEquivFixedGeometricPoint K H A).symm

end FixedFieldPoints

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
