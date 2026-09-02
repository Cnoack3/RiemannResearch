/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightCorestrictionLinkedReduction

/-!
# Affine corestriction-fibre reduction for the hard E7 boundary

For a fixed quadratic extension and a chosen point `r₀` with prescribed
corestriction `α`, this module identifies the whole corestriction fibre with
an affine image of base-field restriction. The remaining linked-quaternion
condition is exactly a `β`-directed edge in a quaternion-twist locus.

The field-theoretic motivation comes from Lam--Leep--Tignol,
*Biquaternion algebras and quartic extensions*, Publ. Math. IHES 77 (1993),
Theorem 5.12, and Arason's restriction--corestriction exact sequence. Those
results provide, in characteristic different from two and cohomological
2-dimension at most two, a quaternion basepoint and middle exactness. They are
not themselves formalized here.

The module also proves that the split quadratic-etale branch is exactly the
previous four-quaternion completion problem and corrects the final E7 bridge
so that the quadratic extension and its transfer data may vary with the target
quaternion triple.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w

variable {A : Type u} {B : Type v}
variable [hA : AddCommGroup A] [AddCommGroup B]

/-! ## The split quadratic-etale branch -/

/-- Diagonal restriction for the split quadratic etale algebra. -/
def splitRestriction : A →+ A × A where
  toFun a := (a, a)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Addition of the two components is corestriction from the split
quadratic etale algebra. -/
def splitCorestriction : A × A →+ A where
  toFun p := p.1 + p.2
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add]
    abel

/-- The nontrivial automorphism of the split quadratic etale algebra exchanges
its two factors. -/
def splitConjugation : A × A →+ A × A where
  toFun p := (p.2, p.1)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The Brauer transfer model of the split quadratic etale algebra. -/
def splitQuadraticBrauerTransferModel :
    QuadraticBrauerTransferModel A (A × A) where
  res := splitRestriction
  cor := splitCorestriction
  conjugate := splitConjugation
  res_cor x := by
    apply Prod.ext
    · rfl
    · exact add_comm x.1 x.2
  cor_res _ := rfl
  conjugate_res _ := rfl

/-- Quaternion classes over a product are quaternion in each component. -/
def ComponentwiseQuaternionClasses
    (IsQuaternionClass : A → Prop) (p : A × A) : Prop :=
  IsQuaternionClass p.1 ∧ IsQuaternionClass p.2

/-- The split quadratic-etale linked-lift construction is exactly the old
four-quaternion completion problem. Thus the split branch supplies no new
flexibility beyond that completion route. -/
theorem splitLinkedLift_iff_quaternionCompletion
    (h₂ : IsExponentTwo A)
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) :
    HasCorestrictionLinkedLiftForTriple
        splitQuadraticBrauerTransferModel
        (ComponentwiseQuaternionClasses IsQuaternionClass)
        q₁ q₂ q₃ ↔
      HasQuaternionCompletion IsQuaternionClass q₁ q₂ q₃ := by
  constructor
  · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, hcor, htranslate⟩
    change r + u = q₂ + q₃ at hcor
    change
      IsQuaternionClass (r + (q₁ + q₂)) ∧
      IsQuaternionClass (u + (q₁ + q₂)) at htranslate
    have hu_eq : u = r + q₂ + q₃ := by
      calc
        u = (r + r) + u := by rw [h₂ r, zero_add]
        _ = r + (r + u) := by abel
        _ = r + (q₂ + q₃) := by rw [hcor]
        _ = r + q₂ + q₃ := by abel
    have hlast :
        (r + q₂ + q₃) + (q₁ + q₂) = r + q₁ + q₃ := by
      calc
        (r + q₂ + q₃) + (q₁ + q₂) =
            r + q₁ + (q₂ + q₂) + q₃ := by abel
        _ = r + q₁ + q₃ := by rw [h₂ q₂]; simp
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · rw [← hu_eq]
      exact hu
    · simpa [add_assoc] using htranslate.1
    · rw [hu_eq, hlast] at htranslate
      exact htranslate.2
  · rintro ⟨r, hr, h₂₃, h₁₂, h₁₃⟩
    refine ⟨(r, r + q₂ + q₃), ⟨hr, h₂₃⟩, ?_, ?_⟩
    · change r + (r + q₂ + q₃) = q₂ + q₃
      calc
        r + (r + q₂ + q₃) = (r + r) + q₂ + q₃ := by abel
        _ = q₂ + q₃ := by rw [h₂ r]; simp
    · change
        IsQuaternionClass (r + (q₁ + q₂)) ∧
        IsQuaternionClass ((r + q₂ + q₃) + (q₁ + q₂))
      constructor
      · simpa [add_assoc] using h₁₂
      · have hlast :
            (r + q₂ + q₃) + (q₁ + q₂) = r + q₁ + q₃ := by
          calc
            (r + q₂ + q₃) + (q₁ + q₂) =
                r + q₁ + (q₂ + q₂) + q₃ := by abel
            _ = r + q₁ + q₃ := by rw [h₂ q₂]; simp
        rw [hlast]
        exact h₁₃

/-! ## Affine corestriction fibres and the residual twist edge -/

/-- A correction in the corestriction kernel makes two points separated by
`res β` quaternion classes in the corestriction fibre through `r₀`. -/
def HasCorestrictionKernelQuaternionEdge
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) (r₀ : B) (β : A) : Prop :=
  ∃ k : B,
    T.cor k = 0 ∧
      IsQuaternionClassB (r₀ + k) ∧
      IsQuaternionClassB (r₀ + k + T.res β)

/-- After choosing any point of the prescribed corestriction fibre, the
linked-lift problem is exactly a quaternion edge inside `ker cor`. -/
theorem hasCorestrictionLinkedQuaternionLift_iff_kernelEdge
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) (α β : A) (r₀ : B)
    (hcor₀ : T.cor r₀ = α) :
    HasCorestrictionLinkedQuaternionLift T IsQuaternionClassB α β ↔
      HasCorestrictionKernelQuaternionEdge
        T IsQuaternionClassB r₀ β := by
  constructor
  · rintro ⟨r, hr, hcor, hrs⟩
    refine ⟨r - r₀, ?_, ?_, ?_⟩
    · rw [map_sub, hcor, hcor₀, sub_self]
    · have heq : r₀ + (r - r₀) = r := by abel
      rwa [heq]
    · have heq : r₀ + (r - r₀) + T.res β = r + T.res β := by abel
      rwa [heq]
  · rintro ⟨k, hk, hr, hrs⟩
    refine ⟨r₀ + k, hr, ?_, hrs⟩
    rw [map_add, hcor₀, hk, add_zero]

/-- The kernel-edge criterion is independent of the chosen basepoint in the
same corestriction fibre. -/
theorem hasCorestrictionKernelQuaternionEdge_basepoint_iff
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) (α β : A) (r₀ r₁ : B)
    (hcor₀ : T.cor r₀ = α) (hcor₁ : T.cor r₁ = α) :
    HasCorestrictionKernelQuaternionEdge T IsQuaternionClassB r₀ β ↔
      HasCorestrictionKernelQuaternionEdge T IsQuaternionClassB r₁ β := by
  calc
    HasCorestrictionKernelQuaternionEdge T IsQuaternionClassB r₀ β ↔
        HasCorestrictionLinkedQuaternionLift T IsQuaternionClassB α β :=
      (hasCorestrictionLinkedQuaternionLift_iff_kernelEdge
        T IsQuaternionClassB α β r₀ hcor₀).symm
    _ ↔ HasCorestrictionKernelQuaternionEdge
          T IsQuaternionClassB r₁ β :=
      hasCorestrictionLinkedQuaternionLift_iff_kernelEdge
        T IsQuaternionClassB α β r₁ hcor₁

/-- Exactness at the quadratic-extension Brauer group: every class with
trivial corestriction is restricted from the base. -/
def CorestrictionKernelIsRestrictionImage
    (T : QuadraticBrauerTransferModel A B) : Prop :=
  ∀ k : B, T.cor k = 0 → ∃ γ : A, T.res γ = k

/-- Under exponent two on the base, the one-sided exactness predicate is the
usual equality between the corestriction kernel and the restriction image. -/
theorem corestriction_eq_zero_iff_exists_restriction
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (k : B) :
    T.cor k = 0 ↔ ∃ γ : A, T.res γ = k := by
  constructor
  · exact hexact k
  · rintro ⟨γ, rfl⟩
    rw [T.cor_res, hA₂ γ]

/-- Under middle exactness, a nonempty corestriction fibre is the affine
restriction image based at any chosen point of that fibre. -/
theorem corestrictionFiber_iff_exists_restrictedTwist
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (α : A) (r₀ : B) (h₀ : T.cor r₀ = α)
    (r : B) :
    T.cor r = α ↔ ∃ γ : A, r = r₀ + T.res γ := by
  constructor
  · intro hcor
    have hk : T.cor (r - r₀) = 0 := by
      rw [map_sub, hcor, h₀, sub_self]
    rcases hexact (r - r₀) hk with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    rw [hγ]
    abel
  · rintro ⟨γ, rfl⟩
    rw [map_add, h₀, T.cor_res, hA₂ γ, add_zero]

/-- Two twist parameters give the same point of the affine fibre exactly when
their difference lies in the restriction kernel. -/
theorem restrictedTwist_eq_iff_res_sub_eq_zero
    (T : QuadraticBrauerTransferModel A B)
    (r₀ : B) (γ δ : A) :
    r₀ + T.res γ = r₀ + T.res δ ↔
      T.res (γ - δ) = 0 := by
  rw [add_left_cancel_iff, map_sub, sub_eq_zero]

/-- Base-field twists whose restriction translates a fixed corestriction
basepoint to a quaternion class. -/
def QuaternionTwistLocus
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) (r₀ : B) : Set A :=
  {γ | IsQuaternionClassB (r₀ + T.res γ)}

/-- If the restriction--corestriction sequence is exact at the extension
Brauer group, the prescribed-corestriction problem is exactly the existence
of a beta-directed edge in the quaternion-twist locus. -/
theorem hasCorestrictionLinkedQuaternionLift_iff_twist_edge
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (IsQuaternionClassB : B → Prop)
    (α β : A) (r₀ : B) (h₀ : T.cor r₀ = α) :
    HasCorestrictionLinkedQuaternionLift T IsQuaternionClassB α β ↔
      ∃ γ : A,
        γ ∈ QuaternionTwistLocus T IsQuaternionClassB r₀ ∧
          γ + β ∈ QuaternionTwistLocus
            T IsQuaternionClassB r₀ := by
  constructor
  · rintro ⟨r, hr, hcor, hs⟩
    have hk : T.cor (r - r₀) = 0 := by
      rw [map_sub, hcor, h₀, sub_self]
    rcases hexact (r - r₀) hk with ⟨γ, hγ⟩
    refine ⟨γ, ?_, ?_⟩
    · change IsQuaternionClassB (r₀ + T.res γ)
      rw [hγ]
      convert hr using 1
      abel
    · change IsQuaternionClassB (r₀ + T.res (γ + β))
      rw [map_add, hγ]
      convert hs using 1
      abel
  · rintro ⟨γ, hγ, hγβ⟩
    change IsQuaternionClassB (r₀ + T.res γ) at hγ
    change IsQuaternionClassB (r₀ + T.res (γ + β)) at hγβ
    refine ⟨r₀ + T.res γ, hγ, ?_, ?_⟩
    · rw [map_add, h₀, T.cor_res, hA₂ γ, add_zero]
    · convert hγβ using 1
      rw [map_add]
      abel

/-- Conjugation is an involution already from the transfer identities; no
exponent-two hypothesis is required. -/
theorem conjugate_involutive
    (T : QuadraticBrauerTransferModel A B) (r : B) :
    T.conjugate (T.conjugate r) = r := by
  have hfixed :
      T.conjugate (r + T.conjugate r) =
        r + T.conjugate r := by
    rw [← T.res_cor r, T.conjugate_res]
  rw [map_add] at hfixed
  calc
    T.conjugate (T.conjugate r) =
        (T.conjugate r + T.conjugate (T.conjugate r)) -
          T.conjugate r := by abel
    _ = (r + T.conjugate r) - T.conjugate r := by rw [hfixed]
    _ = r := by abel

/-- On an exponent-two corestriction fibre, conjugation is translation by the
restriction of the common corestriction class. -/
theorem conjugate_eq_add_res_of_corestriction
    (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (r : B) (α : A) (hcor : T.cor r = α) :
    T.conjugate r = r + T.res α := by
  have hsum : T.res α = r + T.conjugate r := by
    rw [← hcor]
    exact T.res_cor r
  calc
    T.conjugate r = 0 + T.conjugate r := by simp
    _ = (r + r) + T.conjugate r := by rw [hB₂ r]
    _ = r + (r + T.conjugate r) := by abel
    _ = r + T.res α := by rw [← hsum]

/-- Conjugation stability makes the twist-quaternion locus stable under
translation by the corestriction class. -/
theorem mem_quaternionTwistLocus_add_corestriction
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop)
    (hconj : ConjugationPreservesQuaternionClasses
      T IsQuaternionClassB)
    (r₀ : B) (α : A) (h₀ : T.cor r₀ = α)
    (γ : A)
    (hγ : γ ∈ QuaternionTwistLocus
      T IsQuaternionClassB r₀) :
    γ + α ∈ QuaternionTwistLocus
      T IsQuaternionClassB r₀ := by
  change IsQuaternionClassB (r₀ + T.res γ) at hγ
  change IsQuaternionClassB (r₀ + T.res (γ + α))
  have hcor : T.cor (r₀ + T.res γ) = α := by
    rw [map_add, h₀, T.cor_res, hA₂ γ, add_zero]
  have hqc := hconj (r₀ + T.res γ) hγ
  rw [conjugate_eq_add_res_of_corestriction
    hB₂ T (r₀ + T.res γ) α hcor] at hqc
  convert hqc using 1
  rw [map_add]
  abel

/-- Translation by the corestriction class preserves the twist-quaternion
locus in both directions. -/
theorem mem_quaternionTwistLocus_add_corestriction_iff
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop)
    (hconj : ConjugationPreservesQuaternionClasses
      T IsQuaternionClassB)
    (r₀ : B) (α : A) (h₀ : T.cor r₀ = α)
    (γ : A) :
    γ + α ∈ QuaternionTwistLocus
        T IsQuaternionClassB r₀ ↔
      γ ∈ QuaternionTwistLocus
        T IsQuaternionClassB r₀ := by
  constructor
  · intro h
    have h' := mem_quaternionTwistLocus_add_corestriction
      hA₂ hB₂ T IsQuaternionClassB hconj r₀ α h₀
        (γ + α) h
    have heq : (γ + α) + α = γ := by
      calc
        (γ + α) + α = γ + (α + α) := by abel
        _ = γ := by rw [hA₂ α, add_zero]
    rwa [heq] at h'
  · exact mem_quaternionTwistLocus_add_corestriction
      hA₂ hB₂ T IsQuaternionClassB hconj r₀ α h₀ γ

/-! ## Per-packet quadratic extensions -/

/-- Per-packet implementation of the quadratic-transfer construction. Unlike
the fixed-transfer endpoint, the quadratic-extension Brauer group, transfer
model, quaternion predicate, and common-discriminant constructor may all depend
on the target pair `(α, β)`. -/
structure VariableCorestrictionLinkedRealizationWitness
    (C : BoundaryRealization.{u, w} A) (α β : A) where
  B : Type v
  addCommGroupB : AddCommGroup B
  transfer :
    @QuadraticBrauerTransferModel A B hA addCommGroupB
  IsQuaternionClassB : B → Prop
  commonDiscriminant :
    @CommonDiscriminantSumConstructor A B hA addCommGroupB
      C transfer IsQuaternionClassB
  linked :
    @HasCorestrictionLinkedQuaternionLift A B hA addCommGroupB
      transfer IsQuaternionClassB α β

/-- A variable quadratic-transfer witness makes its balanced target packet
effective. -/
theorem BoundaryRealization.isEffective_of_variableCorestrictionLinkedWitness
    (C : BoundaryRealization.{u, w} A) (α β : A)
    (W : VariableCorestrictionLinkedRealizationWitness.{u, v, w} C α β) :
    C.IsEffective
      { underlying := α
        cliffordPlus := β
        cliffordMinus := α + β } := by
  exact @BoundaryRealization.isEffective_of_corestrictionLinkedLift
    A W.B hA W.addCommGroupB C W.transfer W.IsQuaternionClassB
      W.commonDiscriminant α β W.linked

/-- The exact hard-stratum goal allowing the quadratic transfer data to vary
with the prescribed quaternion triple. -/
def IndexEightVariableCorestrictionLinkedRealizationGoal
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, w} A)
    (IsQuaternionClassA : A → Prop) : Prop :=
  ∀ q₁ q₂ q₃ : A,
    IsQuaternionClassA q₁ →
      IsQuaternionClassA q₂ →
        IsQuaternionClassA q₃ →
          I.index (q₁ + q₂ + q₃) = 8 →
            Nonempty
              (VariableCorestrictionLinkedRealizationWitness.{u, v, w}
                C (q₂ + q₃) (q₁ + q₂))

/-- Per-triple quadratic-extension witnesses suffice for the hard E7
realization goal; no single extension or transfer model is required uniformly
over all triples. -/
theorem e7IndexEightRealizationGoal_of_variableCorestrictionLinkedRealizations
    (hA₂ : IsExponentTwo A)
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, w} A)
    (IsQuaternionClassA : A → Prop)
    (h :
      IndexEightVariableCorestrictionLinkedRealizationGoal.{u, v, w}
        I C IsQuaternionClassA) :
    E7IndexEightRealizationGoal I C IsQuaternionClassA := by
  intro q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
  rcases h q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex with ⟨W⟩
  rcases C.isEffective_of_variableCorestrictionLinkedWitness
      (q₂ + q₃) (q₁ + q₂) W with ⟨X, hX⟩
  refine ⟨X, hX.trans ?_⟩
  apply BrauerPacket.ext
  · rfl
  · rfl
  · exact target_underlying_add_plus hA₂ q₁ q₂ q₃

end RiemannResearch.E7.QuaternionTrialityPacket
