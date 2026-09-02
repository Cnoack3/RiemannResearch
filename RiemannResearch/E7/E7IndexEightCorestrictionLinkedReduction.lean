/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightBoundary

/-!
# Corestriction-linked quaternion reduction for the hard E7 boundary

This module isolates the Brauer-group calculation behind a common-discriminant
Dejaiffe-sum construction. It does not assert that the required quaternion
lift exists, nor does it internalize algebras with involution.

For a quadratic étale extension, the published external input is the
degree-four exceptional Clifford correspondence together with the
Lewis--Tignol/Dejaiffe computation of the Clifford components of an orthogonal
sum. In characteristic different from two, those results identify the
remaining construction problem with finding a quaternion class r over the
quadratic extension such that cor r = α and both r and r + res β are
quaternion classes. The verified statements below formalize the exact transfer
identities and the resulting effectivity bridge, conditional only on a
constructor implementing that published algebra-with-involution input.

The module also identifies the lift condition with a factorization problem:
`res β` must be the sum of two quaternion classes over the quadratic
extension, one having corestriction `α`. The other factor then automatically
has the same corestriction. Finally, the condition is shown to be invariant
under swapping the two Clifford labels `β` and `α + β`.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v

variable {A : Type u} {B : Type v}
variable [AddCommGroup A] [AddCommGroup B]

/-- Restriction, corestriction, and nontrivial conjugation on two-primary
Brauer classes for a quadratic étale extension. -/
structure QuadraticBrauerTransferModel
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] where
  res : A →+ B
  cor : B →+ A
  conjugate : B →+ B
  res_cor : ∀ x : B, res (cor x) = x + conjugate x
  cor_res : ∀ a : A, cor (res a) = a + a
  conjugate_res : ∀ a : A, conjugate (res a) = res a

/-- The remaining rank-one-style linkage condition: a quaternion class above
α whose translate by res β is again a quaternion class. -/
def HasCorestrictionLinkedQuaternionLift
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) (α β : A) : Prop :=
  ∃ r : B,
    IsQuaternionClassB r ∧
      T.cor r = α ∧
      IsQuaternionClassB (r + T.res β)

/-- Factor form of the linked-lift condition: `res β` decomposes into two
quaternion classes, with the first factor having corestriction `α`.

For the quadratic Brauer transfer identities, the second factor automatically
has corestriction `α`; see
`corestrictionQuaternionFactorization_second_corestriction`. -/
def HasCorestrictionQuaternionFactorization
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) (α β : A) : Prop :=
  ∃ r s : B,
    IsQuaternionClassB r ∧
      IsQuaternionClassB s ∧
      T.cor r = α ∧
      r + s = T.res β

/-- Over an exponent-two target Brauer group, the one-witness linked-lift
condition is exactly the two-factor decomposition of `res β`. -/
theorem hasCorestrictionLinkedQuaternionLift_iff_factorization
    (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) (α β : A) :
    HasCorestrictionLinkedQuaternionLift T IsQuaternionClassB α β ↔
      HasCorestrictionQuaternionFactorization
        T IsQuaternionClassB α β := by
  constructor
  · rintro ⟨r, hr, hcor, hs⟩
    refine ⟨r, r + T.res β, hr, hs, hcor, ?_⟩
    calc
      r + (r + T.res β) = (r + r) + T.res β := by abel
      _ = T.res β := by rw [hB₂ r, zero_add]
  · rintro ⟨r, s, hr, hs, hcor, hsum⟩
    refine ⟨r, hr, hcor, ?_⟩
    have hrs : r + T.res β = s := by
      calc
        r + T.res β = r + (r + s) := by rw [hsum]
        _ = (r + r) + s := by abel
        _ = s := by rw [hB₂ r, zero_add]
    rw [hrs]
    exact hs

/-- The linkage condition specialized to the underlying and first Clifford
classes of the packet attached to a quaternion triple. -/
def HasCorestrictionLinkedLiftForTriple
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) (q₁ q₂ q₃ : A) : Prop :=
  HasCorestrictionLinkedQuaternionLift
    T IsQuaternionClassB (q₂ + q₃) (q₁ + q₂)

/-- A linked witness produces the two restricted Clifford classes predicted by
the common-discriminant orthogonal-sum calculation. -/
theorem corestrictionLinkedWitness_identities
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (r : B) (α β : A) (hcor : T.cor r = α) :
    let s := r + T.res β
    T.cor s = α ∧
      r + s = T.res β ∧
      r + T.conjugate s = T.res (α + β) := by
  dsimp only
  constructor
  · rw [map_add, hcor, T.cor_res, hA₂ β, add_zero]
  constructor
  · calc
      r + (r + T.res β) = (r + r) + T.res β := by abel
      _ = T.res β := by rw [hB₂ r, zero_add]
  · calc
      r + T.conjugate (r + T.res β) =
          (r + T.conjugate r) + T.res β := by
            rw [map_add, T.conjugate_res]
            abel
      _ = T.res (T.cor r) + T.res β := by rw [T.res_cor]
      _ = T.res α + T.res β := by rw [hcor]
      _ = T.res (α + β) := by rw [map_add]

/-- In a quaternion factorization of `res β`, both factors have
corestriction `α`; it is enough to impose the condition on one factor. -/
theorem corestrictionQuaternionFactorization_second_corestriction
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) (α β : A)
    (h : HasCorestrictionQuaternionFactorization
      T IsQuaternionClassB α β) :
    ∃ r s : B,
      IsQuaternionClassB r ∧
        IsQuaternionClassB s ∧
        T.cor r = α ∧
        T.cor s = α ∧
        r + s = T.res β := by
  rcases h with ⟨r, s, hr, hs, hcor, hsum⟩
  have hrs : r + T.res β = s := by
    calc
      r + T.res β = r + (r + s) := by rw [hsum]
      _ = (r + r) + s := by abel
      _ = s := by rw [hB₂ r, zero_add]
  refine ⟨r, s, hr, hs, hcor, ?_, hsum⟩
  calc
    T.cor s = T.cor (r + T.res β) := by rw [hrs]
    _ = T.cor r + T.cor (T.res β) := by rw [map_add]
    _ = α + (β + β) := by rw [hcor, T.cor_res]
    _ = α := by rw [hA₂ β, add_zero]

/-- Corestriction is invariant under the nontrivial automorphism of a
quadratic étale algebra on exponent-two Brauer classes. This is derived from
the restriction--corestriction identities rather than added as a field of the
transfer model. -/
theorem corestriction_conjugate
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B) (r : B) :
    T.cor (T.conjugate r) = T.cor r := by
  have hsum :
      T.cor r + T.cor (T.conjugate r) = 0 := by
    calc
      T.cor r + T.cor (T.conjugate r) =
          T.cor (r + T.conjugate r) := by rw [map_add]
      _ = T.cor (T.res (T.cor r)) := by rw [T.res_cor]
      _ = T.cor r + T.cor r := by rw [T.cor_res]
      _ = 0 := hA₂ (T.cor r)
  calc
    T.cor (T.conjugate r) =
        T.cor (T.conjugate r) + 0 := by simp
    _ = T.cor (T.conjugate r) + (T.cor r + T.cor r) := by
      rw [hA₂ (T.cor r)]
    _ = (T.cor r + T.cor (T.conjugate r)) + T.cor r := by abel
    _ = 0 + T.cor r := by rw [hsum]
    _ = T.cor r := by simp

/-- The quaternion-class locus over the quadratic extension is stable under
the nontrivial automorphism. -/
def ConjugationPreservesQuaternionClasses
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) : Prop :=
  ∀ r : B, IsQuaternionClassB r →
    IsQuaternionClassB (T.conjugate r)

/-- Conjugating a linked quaternion witness swaps the two Clifford labels. -/
theorem hasCorestrictionLinkedQuaternionLift_swap
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop)
    (hconj : ConjugationPreservesQuaternionClasses T IsQuaternionClassB)
    (α β : A) :
    HasCorestrictionLinkedQuaternionLift T IsQuaternionClassB α β →
      HasCorestrictionLinkedQuaternionLift
        T IsQuaternionClassB α (α + β) := by
  rintro ⟨r, hr, hcor, hs⟩
  refine ⟨T.conjugate r, hconj r hr, ?_, ?_⟩
  · rw [corestriction_conjugate hA₂ T r, hcor]
  · have hresα : T.res α = r + T.conjugate r := by
      rw [← hcor]
      exact T.res_cor r
    have heq :
        T.conjugate r + T.res (α + β) =
          r + T.res β := by
      rw [map_add, hresα]
      calc
        T.conjugate r + ((r + T.conjugate r) + T.res β) =
            r + (T.conjugate r + T.conjugate r) + T.res β := by abel
        _ = r + T.res β := by rw [hB₂ (T.conjugate r)]; simp
    rw [heq]
    exact hs

/-- The corestriction-linked criterion depends only on the unordered
Clifford pair `{β, α + β}`. -/
theorem hasCorestrictionLinkedQuaternionLift_swap_iff
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop)
    (hconj : ConjugationPreservesQuaternionClasses T IsQuaternionClassB)
    (α β : A) :
    HasCorestrictionLinkedQuaternionLift T IsQuaternionClassB α β ↔
      HasCorestrictionLinkedQuaternionLift
        T IsQuaternionClassB α (α + β) := by
  constructor
  · exact hasCorestrictionLinkedQuaternionLift_swap
      hA₂ hB₂ T IsQuaternionClassB hconj α β
  · intro h
    have h' := hasCorestrictionLinkedQuaternionLift_swap
      hA₂ hB₂ T IsQuaternionClassB hconj α (α + β) h
    have hlabel : α + (α + β) = β := by
      calc
        α + (α + β) = (α + α) + β := by abel
        _ = β := by rw [hA₂ α, zero_add]
    rw [hlabel] at h'
    exact h'

/-- In an exponent-two Brauer group, the third label of a quaternion-triple
packet is the sum of the first two labels. -/
theorem target_underlying_add_plus
    (hA₂ : IsExponentTwo A) (q₁ q₂ q₃ : A) :
    (BrauerPacket.ofTriple q₁ q₂ q₃).underlying +
        (BrauerPacket.ofTriple q₁ q₂ q₃).cliffordPlus =
      (BrauerPacket.ofTriple q₁ q₂ q₃).cliffordMinus := by
  change (q₂ + q₃) + (q₁ + q₂) = q₁ + q₃
  calc
    (q₂ + q₃) + (q₁ + q₂) = q₁ + (q₂ + q₂) + q₃ := by abel
    _ = q₁ + q₃ := by rw [hA₂ q₂]; simp

/-- The transfer identities specialized to Gille's three quaternion inputs. -/
theorem corestrictionLinkedWitness_target_identities
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (q₁ q₂ q₃ : A) (r : B)
    (hcor : T.cor r = q₂ + q₃) :
    let s := r + T.res (q₁ + q₂)
    T.cor s = q₂ + q₃ ∧
      r + s = T.res (q₁ + q₂) ∧
      r + T.conjugate s = T.res (q₁ + q₃) := by
  have h := corestrictionLinkedWitness_identities
    hA₂ hB₂ T r (q₂ + q₃) (q₁ + q₂) hcor
  dsimp only at h ⊢
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2]
  apply congrArg T.res
  exact target_underlying_add_plus hA₂ q₁ q₂ q₃

/-- Abstract implementation of the common-discriminant Dejaiffe-sum
construction. Supplying this structure is where the characteristic-not-two
exceptional Clifford correspondence and the scalar-twist descent calculation
enter; no such constructor is assumed here. -/
structure CommonDiscriminantSumConstructor
    (C : BoundaryRealization A)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop) where
  realize : ∀ α β : A,
    HasCorestrictionLinkedQuaternionLift T IsQuaternionClassB α β →
      C.Object
  packet_realize : ∀ (α β : A)
      (h : HasCorestrictionLinkedQuaternionLift
        T IsQuaternionClassB α β),
    C.packet (realize α β h) =
      { underlying := α
        cliffordPlus := β
        cliffordMinus := α + β }

/-- One corestriction-linked quaternion lift makes its balanced packet
effective through a supplied common-discriminant constructor. -/
theorem BoundaryRealization.isEffective_of_corestrictionLinkedLift
    (C : BoundaryRealization A)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop)
    (D : CommonDiscriminantSumConstructor C T IsQuaternionClassB)
    (α β : A)
    (h : HasCorestrictionLinkedQuaternionLift
      T IsQuaternionClassB α β) :
    C.IsEffective
      { underlying := α
        cliffordPlus := β
        cliffordMinus := α + β } := by
  exact ⟨D.realize α β h, D.packet_realize α β h⟩

/-- Uniform linked lifts for the hard quaternion triples imply the exact
index-eight E7 realization goal. This is a reduction, not an assertion that
those lifts exist. -/
theorem e7IndexEightRealizationGoal_of_corestrictionLinkedLifts
    (hA₂ : IsExponentTwo A)
    (I : BrauerIndexModel A)
    (C : BoundaryRealization A)
    (IsQuaternionClassA : A → Prop)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop)
    (D : CommonDiscriminantSumConstructor C T IsQuaternionClassB)
    (hLift : ∀ q₁ q₂ q₃ : A,
      IsQuaternionClassA q₁ →
      IsQuaternionClassA q₂ →
      IsQuaternionClassA q₃ →
      I.index (q₁ + q₂ + q₃) = 8 →
      HasCorestrictionLinkedLiftForTriple
        T IsQuaternionClassB q₁ q₂ q₃) :
    E7IndexEightRealizationGoal I C IsQuaternionClassA := by
  intro q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
  have hLinked : HasCorestrictionLinkedQuaternionLift
      T IsQuaternionClassB (q₂ + q₃) (q₁ + q₂) :=
    hLift q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
  rcases C.isEffective_of_corestrictionLinkedLift
      T IsQuaternionClassB D (q₂ + q₃) (q₁ + q₂) hLinked with
    ⟨X, hX⟩
  refine ⟨X, hX.trans ?_⟩
  apply BrauerPacket.ext
  · rfl
  · rfl
  · exact target_underlying_add_plus hA₂ q₁ q₂ q₃

end RiemannResearch.E7.QuaternionTrialityPacket
