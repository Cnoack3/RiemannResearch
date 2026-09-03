/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightCorestrictionAffineReduction

/-!
# The nondegenerate gauge orbit in the hard E7 corestriction reduction

This module discharges the two non-splitting hypotheses in the gauge-quotient
fixed-point theorem from the hard index-eight packet data.

For a quadratic field extension, every Brauer class killed by restriction has
index dividing two. The abstract predicate
`QuadraticRestrictionKernelHasIndexAtMostTwo` records exactly the numerical
consequence needed here. In the intended field model it follows from the
standard theorem that the index of a central simple algebra divides the degree
of every finite splitting field; see the Stacks Project, Lemma 11.8.4
(tag 074X): <https://stacks.math.columbia.edu/tag/074X>.

Consequently, if the chosen quadratic extension splits the middle quaternion
`q₂` in a quaternion triple of total index eight, it cannot also split
`q₁`, since then it would split the index-four class `q₁ + q₂`. Nor can it
split `q₁ + q₃`, which is itself another index-four packet label. The
residual gauge translation is therefore automatically fixed-point-free.

Combining this fact with the earlier quotient-edge equivalence identifies the
remaining linked-lift condition with a genuinely nondegenerate two-element
orbit in the quotient quaternion locus. This remains a conditional research
reduction: the field-theoretic existence of that orbit is not asserted.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v

variable {A : Type u} {B : Type v}
variable [AddCommGroup A] [AddCommGroup B]

/-- The numerical splitting-field property of a quadratic restriction:
every class killed by restriction has index at most two. -/
def QuadraticRestrictionKernelHasIndexAtMostTwo
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B) : Prop :=
  ∀ a : A, T.res a = 0 → I.index a ≤ 2

/-- In the hard index-eight row, a quadratic restriction splitting the middle
quaternion splits neither the first quaternion nor the opposite packet label.

The only field-theoretic input is
`QuadraticRestrictionKernelHasIndexAtMostTwo`; the rest follows from the
already-verified `(4,4,4)` packet-index theorem. -/
theorem totalIndexEight_middleSplitting_restrictions_nonzero
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassA : A → Prop)
    (hQuaternion :
      QuaternionClassesHaveIndexAtMostTwo I IsQuaternionClassA)
    (hSplitBound : QuadraticRestrictionKernelHasIndexAtMostTwo I T)
    (q₁ q₂ q₃ : A)
    (hq₁ : IsQuaternionClassA q₁)
    (hq₂ : IsQuaternionClassA q₂)
    (hq₃ : IsQuaternionClassA q₃)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8)
    (hMiddle : T.res q₂ = 0) :
    T.res q₁ ≠ 0 ∧ T.res (q₁ + q₃) ≠ 0 := by
  rcases total_index_eight_forces_packet_index_four
      I IsQuaternionClassA hQuaternion q₁ q₂ q₃
        hq₁ hq₂ hq₃ hTotal with
    ⟨_, h₁₂, h₁₃⟩
  change I.index (q₁ + q₂) = 4 at h₁₂
  change I.index (q₁ + q₃) = 4 at h₁₃
  constructor
  · intro h₁
    have hsplit₁₂ : T.res (q₁ + q₂) = 0 := by
      rw [map_add, h₁, hMiddle, add_zero]
    have hle := hSplitBound (q₁ + q₂) hsplit₁₂
    omega
  · intro h₁₃zero
    have hle := hSplitBound (q₁ + q₃) h₁₃zero
    omega

/-- The hard index-eight data make the middle-splitting gauge translation
fixed-point-free; no separate non-splitting assumptions are required. -/
theorem
    totalIndexEight_middleSplitting_twistGaugeQuotientTranslate_fixedPointFree
    (hA₂ : IsExponentTwo A)
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassA : A → Prop)
    (hQuaternion :
      QuaternionClassesHaveIndexAtMostTwo I IsQuaternionClassA)
    (hSplitBound : QuadraticRestrictionKernelHasIndexAtMostTwo I T)
    (q₁ q₂ q₃ : A)
    (hq₁ : IsQuaternionClassA q₁)
    (hq₂ : IsQuaternionClassA q₂)
    (hq₃ : IsQuaternionClassA q₃)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8)
    (hMiddle : T.res q₂ = 0) :
    ∀ q : TwistGaugeQuotient hA₂ T (q₂ + q₃),
      twistGaugeQuotientTranslate hA₂ T
        (q₂ + q₃) (q₁ + q₂) q ≠ q := by
  rcases totalIndexEight_middleSplitting_restrictions_nonzero
      I T IsQuaternionClassA hQuaternion hSplitBound
        q₁ q₂ q₃ hq₁ hq₂ hq₃ hTotal hMiddle with
    ⟨h₁, h₁₃⟩
  exact middleSplitting_twistGaugeQuotientTranslate_fixedPointFree
    hA₂ T q₁ q₂ q₃ hMiddle h₁ h₁₃

/-- A quotient quaternion-locus edge whose two endpoints are distinct. -/
def HasNondegenerateQuaternionTwistQuotientEdge
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassB : B → Prop)
    (hconj : ConjugationPreservesQuaternionClasses T IsQuaternionClassB)
    (r₀ : B) (α β : A) (h₀ : T.cor r₀ = α) : Prop :=
  ∃ q : TwistGaugeQuotient hA₂ T α,
    q ∈ QuaternionTwistQuotientLocus
      hA₂ hB₂ T IsQuaternionClassB hconj r₀ α h₀ ∧
    twistGaugeQuotientTranslate hA₂ T α β q ∈
      QuaternionTwistQuotientLocus
        hA₂ hB₂ T IsQuaternionClassB hconj r₀ α h₀ ∧
    twistGaugeQuotientTranslate hA₂ T α β q ≠ q

/-- For a hard index-eight triple and a quadratic restriction splitting its
middle quaternion, the linked-lift condition is exactly the existence of a
nondegenerate quotient quaternion-locus edge. Since the translation is an
involution, its endpoints form a genuine two-element orbit. -/
theorem
    totalIndexEight_middleSplitting_linkedLift_iff_nondegenerateQuotientEdge
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B)
    (IsQuaternionClassA : A → Prop)
    (hQuaternion :
      QuaternionClassesHaveIndexAtMostTwo I IsQuaternionClassA)
    (hSplitBound : QuadraticRestrictionKernelHasIndexAtMostTwo I T)
    (IsQuaternionClassB : B → Prop)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (hconj : ConjugationPreservesQuaternionClasses T IsQuaternionClassB)
    (q₁ q₂ q₃ : A)
    (hq₁ : IsQuaternionClassA q₁)
    (hq₂ : IsQuaternionClassA q₂)
    (hq₃ : IsQuaternionClassA q₃)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8)
    (hMiddle : T.res q₂ = 0)
    (r₀ : B) (h₀ : T.cor r₀ = q₂ + q₃) :
    HasCorestrictionLinkedLiftForTriple
        T IsQuaternionClassB q₁ q₂ q₃ ↔
      HasNondegenerateQuaternionTwistQuotientEdge
        hA₂ hB₂ T IsQuaternionClassB hconj r₀
          (q₂ + q₃) (q₁ + q₂) h₀ := by
  change
    HasCorestrictionLinkedQuaternionLift
        T IsQuaternionClassB (q₂ + q₃) (q₁ + q₂) ↔ _
  rw [hasCorestrictionLinkedQuaternionLift_iff_quotientTwistEdge
    hA₂ hB₂ T hexact IsQuaternionClassB hconj
      (q₂ + q₃) (q₁ + q₂) r₀ h₀]
  constructor
  · rintro ⟨q, hq, hq'⟩
    refine ⟨q, hq, hq', ?_⟩
    exact
      totalIndexEight_middleSplitting_twistGaugeQuotientTranslate_fixedPointFree
        hA₂ I T IsQuaternionClassA hQuaternion hSplitBound
          q₁ q₂ q₃ hq₁ hq₂ hq₃ hTotal hMiddle q
  · rintro ⟨q, hq, hq', _⟩
    exact ⟨q, hq, hq'⟩

end RiemannResearch.E7.QuaternionTrialityPacket
