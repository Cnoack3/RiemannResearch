/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.GaloisTripleTensorDecomposition
import RiemannResearch.GaloisCohomology.NonabelianH1

/-!
# Galois coordinates for fixed-cover Čech H¹

This file gives the algebraic coordinate comparison underlying the equivalence
between Čech H¹ for a finite Galois cover and discrete nonabelian Galois H¹.

For the right-associated triple overlap

    L ⊗[K] (L ⊗[K] L),

the three maps from the double overlap L ⊗[K] L are defined explicitly.
Under the independent-coordinate Galois decompositions, their values are

    f σ,    f ρ,    σ (f (σ⁻¹ * ρ)).

Consequently, the Čech cocycle equation becomes

    a σ * σ • a (σ⁻¹ * ρ) = a ρ,

which is equivalent, after writing ρ = σ * τ, to the inhomogeneous group
cocycle equation

    a (σ * τ) = a σ * σ • a τ.

The file constructs the equivalence on cocycles, proves compatibility with
gauge transformations, and descends it to a pointed equivalence between the
coordinate Čech H¹ and NonabelianH1.

This is the ring-coordinate and quotient-level core of the fpqc comparison.
Identifying Mathlib's PresheafOfGroups.H1 for the singleton cover
Spec L → Spec K with this coordinate model additionally requires the Yoneda
identification of its natural-family cochains with sections on the affine
fiber products. That representability bridge is not supplied by Mathlib's
current nonabelian H¹ API.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- Pullback from the double overlap to factors zero and one of the triple
overlap. On pure tensors it sends x ⊗ y to x ⊗ (y ⊗ 1). -/
def galoisCechFace01 :
    TensorProduct K L L →ₐ[K]
      TensorProduct K L (TensorProduct K L L) :=
  Algebra.TensorProduct.map
    (AlgHom.id K L)
    (Algebra.TensorProduct.includeLeft :
      L →ₐ[K] TensorProduct K L L)

/-- Pullback from the double overlap to factors zero and two of the triple
overlap. On pure tensors it sends x ⊗ y to x ⊗ (1 ⊗ y). -/
def galoisCechFace02 :
    TensorProduct K L L →ₐ[K]
      TensorProduct K L (TensorProduct K L L) :=
  Algebra.TensorProduct.map
    (AlgHom.id K L)
    (Algebra.TensorProduct.includeRight :
      L →ₐ[K] TensorProduct K L L)

/-- Pullback from the double overlap to factors one and two of the triple
overlap. On pure tensors it sends x ⊗ y to 1 ⊗ (x ⊗ y). -/
def galoisCechFace12 :
    TensorProduct K L L →ₐ[K]
      TensorProduct K L (TensorProduct K L L) :=
  Algebra.TensorProduct.includeRight

/-- Pure-tensor formula for the zero-one face map. -/
@[simp]
theorem galoisCechFace01_tmul (x y : L) :
    galoisCechFace01 K L (x ⊗ₜ[K] y) =
      x ⊗ₜ[K] (y ⊗ₜ[K] (1 : L)) := by
  simp [galoisCechFace01]

/-- Pure-tensor formula for the zero-two face map. -/
@[simp]
theorem galoisCechFace02_tmul (x y : L) :
    galoisCechFace02 K L (x ⊗ₜ[K] y) =
      x ⊗ₜ[K] ((1 : L) ⊗ₜ[K] y) := by
  simp [galoisCechFace02]

/-- Pure-tensor formula for the one-two face map. -/
@[simp]
theorem galoisCechFace12_tmul (x y : L) :
    galoisCechFace12 K L (x ⊗ₜ[K] y) =
      (1 : L) ⊗ₜ[K] (x ⊗ₜ[K] y) := by
  simp [galoisCechFace12]

/-- In independent Galois coordinates, the zero-one face pulls a function
back along the first projection. -/
@[simp]
theorem galoisCechFace01_eval
    [FiniteDimensional K L] [IsGalois K L]
    (z : TensorProduct K L L) (σ ρ : L ≃ₐ[K] L) :
    galoisTripleTensorEquiv K L (galoisCechFace01 K L z) σ ρ =
      galoisTensorEquiv K L z σ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- In independent Galois coordinates, the zero-two face pulls a function
back along the second projection. -/
@[simp]
theorem galoisCechFace02_eval
    [FiniteDimensional K L] [IsGalois K L]
    (z : TensorProduct K L L) (σ ρ : L ≃ₐ[K] L) :
    galoisTripleTensorEquiv K L (galoisCechFace02 K L z) σ ρ =
      galoisTensorEquiv K L z ρ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- In independent Galois coordinates, the one-two face is the twisted
projection f ↦ ((σ, ρ) ↦ σ (f (σ⁻¹ρ))). -/
@[simp]
theorem galoisCechFace12_eval
    [FiniteDimensional K L] [IsGalois K L]
    (z : TensorProduct K L L) (σ ρ : L ≃ₐ[K] L) :
    galoisTripleTensorEquiv K L (galoisCechFace12 K L z) σ ρ =
      σ (galoisTensorEquiv K L z (σ⁻¹ * ρ)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- A one-cocycle written in the independent coordinates of the finite Galois
Čech double and triple overlaps. -/
structure GaloisCechCocycle
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] where
  /-- The function on the Galois-coordinate double overlap. -/
  toFun : Γ → G
  /-- The Čech equation on the triple overlap. -/
  cocycle' : ∀ σ ρ, toFun σ * σ • toFun (σ⁻¹ * ρ) = toFun ρ

instance {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] :
    CoeFun (GaloisCechCocycle Γ G) (fun _ => Γ → G) :=
  ⟨GaloisCechCocycle.toFun⟩

/-- Coordinate Čech cocycles are equal when their functions agree. -/
@[ext]
theorem GaloisCechCocycle.ext
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] {a b : GaloisCechCocycle Γ G}
    (h : ∀ σ, a σ = b σ) : a = b := by
  cases a with
  | mk af ah =>
    cases b with
    | mk bf bh =>
      have hab : af = bf := funext h
      subst bf
      rfl

/-- The Čech equation in independent coordinates is equivalent to the
inhomogeneous nonabelian group-cocycle equation. -/
def galoisCechCocycleEquiv
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] :
    GaloisCechCocycle Γ G ≃ NonabelianCocycle Γ G where
  toFun a :=
    { toFun := a
      map_mul' := by
        intro σ τ
        simpa using (a.cocycle' σ (σ * τ)).symm }
  invFun a :=
    { toFun := a
      cocycle' := by
        intro σ ρ
        simpa using (a.map_mul' σ (σ⁻¹ * ρ)).symm }
  left_inv a := by ext σ; rfl
  right_inv a := by ext σ; rfl

/-- The cocycle equivalence preserves evaluation. -/
@[simp]
theorem galoisCechCocycleEquiv_apply
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : GaloisCechCocycle Γ G) (σ : Γ) :
    galoisCechCocycleEquiv Γ G a σ = a σ :=
  rfl

/-- The inverse cocycle equivalence preserves evaluation. -/
@[simp]
theorem galoisCechCocycleEquiv_symm_apply
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G) (σ : Γ) :
    (galoisCechCocycleEquiv Γ G).symm a σ = a σ :=
  rfl

/-- The trivial coordinate Čech cocycle. -/
def GaloisCechCocycle.trivial
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : GaloisCechCocycle Γ G :=
  (galoisCechCocycleEquiv Γ G).symm NonabelianCocycle.trivial

/-- The trivial coordinate cocycle is pointwise one. -/
@[simp]
theorem GaloisCechCocycle.trivial_apply
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (σ : Γ) :
    (GaloisCechCocycle.trivial : GaloisCechCocycle Γ G) σ = 1 :=
  rfl

/-- Gauge a coordinate Čech cocycle by a zero-cochain. -/
def GaloisCechCocycle.gauge
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (g : G) (a : GaloisCechCocycle Γ G) :
    GaloisCechCocycle Γ G :=
  (galoisCechCocycleEquiv Γ G).symm
    ((galoisCechCocycleEquiv Γ G a).gauge g)

/-- In Galois coordinates, the Čech gauge action is
a σ ↦ g⁻¹ * a σ * σ • g. -/
@[simp]
theorem GaloisCechCocycle.gauge_apply
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (g : G) (a : GaloisCechCocycle Γ G) (σ : Γ) :
    a.gauge g σ = g⁻¹ * a σ * σ • g := by
  rfl

/-- The cocycle equivalence intertwines the Čech and group-cohomology gauge
actions. -/
theorem galoisCechCocycleEquiv_gauge
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (g : G) (a : GaloisCechCocycle Γ G) :
    galoisCechCocycleEquiv Γ G (a.gauge g) =
      (galoisCechCocycleEquiv Γ G a).gauge g := by
  exact (galoisCechCocycleEquiv Γ G).apply_symm_apply _

/-- Gauge equivalence for coordinate Čech cocycles. -/
def GaloisCechCocycle.Cohomologous
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (a b : GaloisCechCocycle Γ G) : Prop :=
  ∃ g : G, b = a.gauge g

/-- The cocycle equivalence preserves and reflects gauge equivalence. -/
theorem galoisCechCocycleEquiv_cohomologous
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a b : GaloisCechCocycle Γ G) :
    a.Cohomologous b ↔
      (galoisCechCocycleEquiv Γ G a).Cohomologous
        (galoisCechCocycleEquiv Γ G b) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, galoisCechCocycleEquiv_gauge g a⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, (galoisCechCocycleEquiv Γ G).injective ?_⟩
    rw [galoisCechCocycleEquiv_gauge]
    exact hg

/-- The setoid of coordinate Čech cocycles modulo zero-cochain gauge. -/
def GaloisCechCocycle.setoid
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : Setoid (GaloisCechCocycle Γ G) where
  r := GaloisCechCocycle.Cohomologous
  iseqv := by
    constructor
    · intro a
      rw [galoisCechCocycleEquiv_cohomologous]
      exact NonabelianCocycle.cohomologous_refl _
    · intro a b h
      rw [galoisCechCocycleEquiv_cohomologous] at h ⊢
      exact NonabelianCocycle.cohomologous_symm h
    · intro a b c hab hbc
      rw [galoisCechCocycleEquiv_cohomologous] at hab hbc ⊢
      exact NonabelianCocycle.cohomologous_trans hab hbc

instance GaloisCechCocycle.instSetoid
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : Setoid (GaloisCechCocycle Γ G) :=
  GaloisCechCocycle.setoid Γ G

/-- Fixed-cover Čech H¹ in finite-Galois coordinates. -/
def GaloisCechH1
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] :=
  Quotient (GaloisCechCocycle.setoid Γ G)

namespace GaloisCechH1

/-- The class of a coordinate Čech cocycle. -/
def classOf
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : GaloisCechCocycle Γ G) :
    GaloisCechH1 Γ G :=
  Quotient.mk' a

/-- The neutral coordinate Čech class. -/
def neutral
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : GaloisCechH1 Γ G :=
  classOf GaloisCechCocycle.trivial

instance instOne
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : One (GaloisCechH1 Γ G) :=
  ⟨neutral⟩

/-- The pointed equivalence from coordinate Čech H¹ to discrete nonabelian
group H¹. -/
def equivNonabelian
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] :
    GaloisCechH1 Γ G ≃ NonabelianH1 Γ G :=
  Quotient.congr (galoisCechCocycleEquiv Γ G)
    (galoisCechCocycleEquiv_cohomologous)

/-- The H¹ equivalence sends a represented Čech class to the corresponding
group-cocycle class. -/
@[simp]
theorem equivNonabelian_classOf
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : GaloisCechCocycle Γ G) :
    equivNonabelian Γ G (classOf a) =
      NonabelianH1.classOf (galoisCechCocycleEquiv Γ G a) :=
  rfl

/-- The H¹ equivalence preserves the distinguished neutral class. -/
@[simp]
theorem equivNonabelian_neutral
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] :
    equivNonabelian Γ G (neutral : GaloisCechH1 Γ G) =
      (NonabelianH1.neutral : NonabelianH1 Γ G) :=
  rfl

end GaloisCechH1

end

end RiemannResearch.GaloisCohomology
