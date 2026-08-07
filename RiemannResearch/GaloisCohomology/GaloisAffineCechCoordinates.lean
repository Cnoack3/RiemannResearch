/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.GaloisCechComparison

/-!
# Affine-group coordinates on finite-Galois Čech overlaps

Let `L/K` be a finite Galois extension and let `A` be a commutative Hopf
algebra over `K`.  This file identifies the `A`-valued points of the
double and triple affine Čech overlaps with functions on the Galois group.

The coefficient group is the convolution group

    G(L) = WithConv (A →ₐ[K] L).

Its Galois action is postcomposition.  Applying the tensor-square and
tensor-cube decompositions pointwise gives multiplicative equivalences

    Hom(A, L ⊗[K] L)             ≃ (Gal(L/K) → G(L)),
    Hom(A, L ⊗[K] (L ⊗[K] L))   ≃ (Gal(L/K) → Gal(L/K) → G(L)).

The three affine Čech face maps become the first projection, second
projection, and twisted projection.  Consequently, an affine-algebra
cocycle on the tensor-square overlap is equivalent to the coordinate Čech
cocycle already used in `GaloisCechComparison`.

No representability assumption is made here.  The remaining scheme-level
step is to transport these algebra homomorphisms through
`AlgebraicGeometry.Spec.mapMulEquiv` and the affine pullback isomorphisms.
-/

namespace RiemannResearch.GaloisCohomology

universe u

noncomputable section

variable (K L A : Type u)
variable [Field K] [Field L] [Algebra K L]
variable [CommRing A] [HopfAlgebra K A]

/-- The convolution group of `L`-points of the affine group represented by
the Hopf algebra `A`. -/
abbrev AffineGaloisPoint :=
  WithConv (A →ₐ[K] L)

/-- Galois automorphisms act on affine points by postcomposition. -/
def affineGaloisPointSMul
    (σ : L ≃ₐ[K] L) (f : AffineGaloisPoint K L A) :
    AffineGaloisPoint K L A :=
  WithConv.toConv (σ.toAlgHom.comp f.ofConv)

instance instSMulAffineGaloisPoint :
    SMul (L ≃ₐ[K] L) (AffineGaloisPoint K L A) :=
  ⟨affineGaloisPointSMul K L A⟩

instance instMulActionAffineGaloisPoint :
    MulAction (L ≃ₐ[K] L) (AffineGaloisPoint K L A) where
  one_smul := by
    intro f
    change affineGaloisPointSMul K L A 1 f = f
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro x
    change (1 : L ≃ₐ[K] L) (f.ofConv x) = f.ofConv x
    exact AlgEquiv.one_apply _
  mul_smul := by
    intro σ τ f
    change
      affineGaloisPointSMul K L A (σ * τ) f =
        affineGaloisPointSMul K L A σ
          (affineGaloisPointSMul K L A τ f)
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro x
    change (σ * τ) (f.ofConv x) = σ (τ (f.ofConv x))
    exact AlgEquiv.mul_apply _ _ _

instance instMulDistribMulActionAffineGaloisPoint :
    MulDistribMulAction (L ≃ₐ[K] L) (AffineGaloisPoint K L A) where
  smul_mul := by
    intro σ f g
    change
      affineGaloisPointSMul K L A σ (f * g) =
        affineGaloisPointSMul K L A σ f *
          affineGaloisPointSMul K L A σ g
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib σ.toAlgHom f g
  smul_one := by
    intro σ
    change affineGaloisPointSMul K L A σ 1 = 1
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro x
    simp [affineGaloisPointSMul]

/-- Postcomposition by an algebra equivalence is a multiplicative equivalence
between convolution groups of algebra homomorphisms. -/
def convPostcompMulEquiv
    {B C : Type u} [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] (e : B ≃ₐ[K] C) :
    WithConv (A →ₐ[K] B) ≃* WithConv (A →ₐ[K] C) where
  toFun := fun f => WithConv.toConv (e.toAlgHom.comp f.ofConv)
  invFun := fun f => WithConv.toConv (e.symm.toAlgHom.comp f.ofConv)
  left_inv := by
    intro f
    apply WithConv.ofConv_injective
    ext x
    simp
  right_inv := by
    intro f
    apply WithConv.ofConv_injective
    ext x
    simp
  map_mul' := by
    intro f g
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib e.toAlgHom f g

/-- Algebra maps into a function algebra are pointwise families of algebra
maps, compatibly with convolution multiplication. -/
def convAlgHomPiMulEquiv (ι : Type u) :
    WithConv (A →ₐ[K] (ι → L)) ≃*
      (ι → AffineGaloisPoint K L A) where
  toFun := fun f i =>
    WithConv.toConv
      ((Pi.evalAlgHom K (fun _ : ι => L) i).comp f.ofConv)
  invFun := fun f =>
    WithConv.toConv (AlgHom.pi (fun i => (f i).ofConv))
  left_inv := by
    intro f
    apply WithConv.ofConv_injective
    ext x i
    rfl
  right_inv := by
    intro f
    funext i
    apply WithConv.ofConv_injective
    ext x
    rfl
  map_mul' := by
    intro f g
    funext i
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib
      (Pi.evalAlgHom K (fun _ : ι => L) i) f g

/-- The two-variable version of `convAlgHomPiMulEquiv`. -/
def convAlgHomPiPiMulEquiv (ι κ : Type u) :
    WithConv (A →ₐ[K] (ι → κ → L)) ≃*
      (ι → κ → AffineGaloisPoint K L A) where
  toFun := fun f i j =>
    WithConv.toConv
      ((Pi.evalAlgHom K (fun _ : κ => L) j).comp
        ((Pi.evalAlgHom K (fun _ : ι => κ → L) i).comp f.ofConv))
  invFun := fun f =>
    WithConv.toConv
      (AlgHom.pi (fun i => AlgHom.pi (fun j => (f i j).ofConv)))
  left_inv := by
    intro f
    apply WithConv.ofConv_injective
    ext x i j
    rfl
  right_inv := by
    intro f
    funext i j
    apply WithConv.ofConv_injective
    ext x
    rfl
  map_mul' := by
    intro f g
    funext i j
    apply WithConv.ofConv_injective
    rw [← AlgHom.comp_assoc]
    exact AlgHom.comp_convMul_distrib
      ((Pi.evalAlgHom K (fun _ : κ => L) j).comp
        (Pi.evalAlgHom K (fun _ : ι => κ → L) i)) f g

/-- Affine-group points on the finite-Galois double overlap are functions from
the Galois group to `L`-points. -/
def galoisDoubleOverlapPointMulEquiv
    [FiniteDimensional K L] [IsGalois K L] :
    WithConv (A →ₐ[K] TensorProduct K L L) ≃*
      ((L ≃ₐ[K] L) → AffineGaloisPoint K L A) :=
  (convPostcompMulEquiv K A
      ((galoisTensorEquiv K L).restrictScalars K)).trans
    (convAlgHomPiMulEquiv K L A (L ≃ₐ[K] L))

/-- Affine-group points on the finite-Galois triple overlap are functions of
two Galois automorphisms. -/
def galoisTripleOverlapPointMulEquiv
    [FiniteDimensional K L] [IsGalois K L] :
    WithConv (A →ₐ[K] TensorProduct K L (TensorProduct K L L)) ≃*
      ((L ≃ₐ[K] L) → (L ≃ₐ[K] L) → AffineGaloisPoint K L A) :=
  (convPostcompMulEquiv K A
      ((galoisTripleTensorEquiv K L).restrictScalars K)).trans
    (convAlgHomPiPiMulEquiv K L A
      (L ≃ₐ[K] L) (L ≃ₐ[K] L))

/-- Evaluation formula for the double-overlap point equivalence. -/
@[simp]
theorem galoisDoubleOverlapPointMulEquiv_apply
    [FiniteDimensional K L] [IsGalois K L]
    (f : WithConv (A →ₐ[K] TensorProduct K L L))
    (σ : L ≃ₐ[K] L) (x : A) :
    ((galoisDoubleOverlapPointMulEquiv K L A f σ).ofConv x) =
      galoisTensorEquiv K L (f.ofConv x) σ :=
  rfl

/-- Evaluation formula for the triple-overlap point equivalence. -/
@[simp]
theorem galoisTripleOverlapPointMulEquiv_apply
    [FiniteDimensional K L] [IsGalois K L]
    (f : WithConv
      (A →ₐ[K] TensorProduct K L (TensorProduct K L L)))
    (σ ρ : L ≃ₐ[K] L) (x : A) :
    ((galoisTripleOverlapPointMulEquiv K L A f σ ρ).ofConv x) =
      galoisTripleTensorEquiv K L (f.ofConv x) σ ρ :=
  rfl

/-- Pull an affine-group point along a homomorphism of coordinate algebras. -/
def pullAffinePointAlong
    {B C : Type u} [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C]
    (h : B →ₐ[K] C) (f : WithConv (A →ₐ[K] B)) :
    WithConv (A →ₐ[K] C) :=
  WithConv.toConv (h.comp f.ofConv)

/-- On affine-group points in Galois coordinates, the zero-one face is the
first projection. -/
@[simp]
theorem galoisCechFace01_point
    [FiniteDimensional K L] [IsGalois K L]
    (f : WithConv (A →ₐ[K] TensorProduct K L L))
    (σ ρ : L ≃ₐ[K] L) :
    galoisTripleOverlapPointMulEquiv K L A
        (pullAffinePointAlong K A (galoisCechFace01 K L) f) σ ρ =
      galoisDoubleOverlapPointMulEquiv K L A f σ := by
  apply WithConv.ofConv_injective
  ext x
  exact galoisCechFace01_eval K L (f.ofConv x) σ ρ

/-- On affine-group points in Galois coordinates, the zero-two face is the
second projection. -/
@[simp]
theorem galoisCechFace02_point
    [FiniteDimensional K L] [IsGalois K L]
    (f : WithConv (A →ₐ[K] TensorProduct K L L))
    (σ ρ : L ≃ₐ[K] L) :
    galoisTripleOverlapPointMulEquiv K L A
        (pullAffinePointAlong K A (galoisCechFace02 K L) f) σ ρ =
      galoisDoubleOverlapPointMulEquiv K L A f ρ := by
  apply WithConv.ofConv_injective
  ext x
  exact galoisCechFace02_eval K L (f.ofConv x) σ ρ

/-- On affine-group points in Galois coordinates, the one-two face is the
twisted projection. -/
@[simp]
theorem galoisCechFace12_point
    [FiniteDimensional K L] [IsGalois K L]
    (f : WithConv (A →ₐ[K] TensorProduct K L L))
    (σ ρ : L ≃ₐ[K] L) :
    galoisTripleOverlapPointMulEquiv K L A
        (pullAffinePointAlong K A (galoisCechFace12 K L) f) σ ρ =
      σ • galoisDoubleOverlapPointMulEquiv K L A f (σ⁻¹ * ρ) := by
  apply WithConv.ofConv_injective
  ext x
  exact galoisCechFace12_eval K L (f.ofConv x) σ ρ

end

end RiemannResearch.GaloisCohomology
