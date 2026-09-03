/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightCorestrictionStableLayerExclusion

/-!
# From an aligned quadratic layer to hard E7 effectivity

The preceding reductions isolate a labelled quadratic layer `U/M` and a
relative Brauer class `r` satisfying

```text
res_U(res_M(q₁)) = 0,
res_U(r) = 0,
cor_M/F(r) = q₂ + q₃,
res_M(q₂) = 0.
```

This module closes the logical gap between that aligned-layer condition and
the original linked-quaternion lift. Since `U/M` is quadratic, every Brauer
class which it splits has index at most two. In the exponent-two setting such
a class is represented by a quaternion algebra (including the split case).
The abstract predicate
`LayerRestrictionKernelConsistsOfQuaternionClasses` records exactly this
standard field-theoretic input. The index-divisibility statement is supported
by the Stacks Project, Lemma 11.8.4 (tag 074X):
<https://stacks.math.columbia.edu/tag/074X>.

Both `r` and `res_M(q₁)` lie in the restriction kernel, so their sum lies
there as well. Because `res_M(q₂)=0`, that sum is precisely

```text
r + res_M(q₁ + q₂).
```

Thus `r` and its required translate are quaternion classes and `r` is the
desired corestriction-linked lift. A supplied common-discriminant
algebra-with-involution constructor then realizes the original labelled
trialitarian packet.

This is a conditional research reduction. It proves that construction of an
aligned quadratic layer is sufficient; it does not assert that such a layer
exists in either of the two remaining nonnormal quartic positions.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w x

variable {A : Type u} {B : Type v} {C : Type w}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Every class split by the quadratic layer is a quaternion class.

For the intended field restriction `Br₂(M) → Br₂(U)` with `[U:M]=2`,
this follows from the standard splitting-field index theorem. -/
def LayerRestrictionKernelConsistsOfQuaternionClasses
    (down : B →+ C) (IsQuaternionClassB : B → Prop) : Prop :=
  ∀ b : B, down b = 0 → IsQuaternionClassB b

/-- An aligned quadratic layer produces the exact corestriction-linked
quaternion lift required for the hard E7 packet.

The two quaternion endpoints are `r` and
`r + res(q₁ + q₂)`; both are split by the same quadratic layer. -/
theorem hasCorestrictionLinkedLiftForTriple_of_alignedLayer
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (hKernelQuaternion :
      LayerRestrictionKernelConsistsOfQuaternionClasses
        down IsQuaternionClassB)
    (q₁ q₂ q₃ : A)
    (hMiddle : T.res q₂ = 0)
    (hAligned : HasAlignedRelativeCorestrictionLayer
      T down q₁ q₂ q₃) :
    HasCorestrictionLinkedLiftForTriple
      T IsQuaternionClassB q₁ q₂ q₃ := by
  rcases hAligned with ⟨r, hq₁U, hrU, hcor⟩
  refine ⟨r, hKernelQuaternion r hrU, hcor, ?_⟩
  apply hKernelQuaternion
  rw [map_add, map_add, hMiddle, add_zero, hrU, hq₁U, zero_add]

/-- An aligned layer, together with the published common-discriminant
constructor represented by `D`, realizes the original labelled packet.

This is the local effectivity endpoint: the extension and aligned layer may be
chosen separately for each quaternion triple. -/
theorem BoundaryRealization.isEffective_of_alignedLayerForTriple
    (hA₂ : IsExponentTwo A)
    (R : BoundaryRealization.{u, x} A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (hKernelQuaternion :
      LayerRestrictionKernelConsistsOfQuaternionClasses
        down IsQuaternionClassB)
    (D : CommonDiscriminantSumConstructor R T IsQuaternionClassB)
    (q₁ q₂ q₃ : A)
    (hMiddle : T.res q₂ = 0)
    (hAligned : HasAlignedRelativeCorestrictionLayer
      T down q₁ q₂ q₃) :
    R.IsEffective (BrauerPacket.ofTriple q₁ q₂ q₃) := by
  have hLinked := hasCorestrictionLinkedLiftForTriple_of_alignedLayer
    T down IsQuaternionClassB hKernelQuaternion
      q₁ q₂ q₃ hMiddle hAligned
  rcases R.isEffective_of_corestrictionLinkedLift
      T IsQuaternionClassB D (q₂ + q₃) (q₁ + q₂) hLinked with
    ⟨X, hX⟩
  refine ⟨X, hX.trans ?_⟩
  apply BrauerPacket.ext
  · rfl
  · rfl
  · exact target_underlying_add_plus hA₂ q₁ q₂ q₃

end RiemannResearch.E7.QuaternionTrialityPacket
