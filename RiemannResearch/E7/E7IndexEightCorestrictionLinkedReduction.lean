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
