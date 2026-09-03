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

/-- A correction lying in both the upper restriction kernel and the
corestriction kernel can be absorbed into an aligned linked pair.

Both translated endpoints remain split by the upper quadratic layer, hence
are quaternion classes under `hKernelQuaternion`. Their common
corestriction and their difference are unchanged. This is the exact abstract
stability needed if a weak Albert transporter contributes a nonzero Brauer
norm class; realizing such a correction algebraically remains external.

The calculation is independent of the Albert interpretation and uses only
the displayed restriction and corestriction kernels. -/
theorem alignedLayerCorrection_preserves_linkedPair
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (hKernelQuaternion :
      LayerRestrictionKernelConsistsOfQuaternionClasses
        down IsQuaternionClassB)
    (q₁ q₂ q₃ : A)
    (hMiddle : T.res q₂ = 0)
    (r δ : B)
    (hq₁U : down (T.res q₁) = 0)
    (hrU : down r = 0)
    (hcor : T.cor r = q₂ + q₃)
    (hδU : down δ = 0)
    (hδcor : T.cor δ = 0) :
    let r' := r + δ
    let s' := r' + T.res (q₁ + q₂)
    IsQuaternionClassB r' ∧
      IsQuaternionClassB s' ∧
      T.cor r' = q₂ + q₃ ∧
      T.cor s' = q₂ + q₃ ∧
      r' + s' = T.res (q₁ + q₂) := by
  dsimp only
  have hr'Quaternion : IsQuaternionClassB (r + δ) := by
    apply hKernelQuaternion
    rw [map_add, hrU, hδU, add_zero]
  have hs'Quaternion :
      IsQuaternionClassB ((r + δ) + T.res (q₁ + q₂)) := by
    apply hKernelQuaternion
    calc
      down ((r + δ) + T.res (q₁ + q₂)) =
          (down r + down δ) +
            (down (T.res q₁) + down (T.res q₂)) := by
              simp only [map_add]
      _ = 0 := by simp [hrU, hδU, hq₁U, hMiddle]
  have hr'cor : T.cor (r + δ) = q₂ + q₃ := by
    rw [map_add, hcor, hδcor, add_zero]
  have hs'cor :
      T.cor ((r + δ) + T.res (q₁ + q₂)) = q₂ + q₃ := by
    rw [map_add, hr'cor, T.cor_res, hA₂, add_zero]
  have hsum :
      (r + δ) + ((r + δ) + T.res (q₁ + q₂)) =
        T.res (q₁ + q₂) := by
    calc
      (r + δ) + ((r + δ) + T.res (q₁ + q₂)) =
          ((r + δ) + (r + δ)) + T.res (q₁ + q₂) := by abel
      _ = T.res (q₁ + q₂) := by rw [hB₂, zero_add]
  exact ⟨hr'Quaternion, hs'Quaternion, hr'cor, hs'cor, hsum⟩

/-- Translation by the restricted opposite packet label preserves the two
split quaternion endpoints and their prescribed corestriction. Applying the
same correction a second time returns to the original endpoint.

Unlike `alignedLayerCorrection_preserves_linkedPair`, this specialization does
not need exponent two on all of `B`: exponent two for `β` in `A` implies that
`T.res β` has order at most two. The conclusion does not assert that the two
endpoints are distinct.

In the corrected LLT orientation, `β` restricts to `q₂` over the quadratic
middle field when that field splits `q₁` (and to `q₃` after the half-spin
swap). The hypothesis `hβU` is therefore exactly the unresolved second-slot
incidence; this theorem does not construct that incidence. -/
theorem oppositeLabelCorrection_swaps_linkedLiftEndpoints
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (hKernelQuaternion :
      LayerRestrictionKernelConsistsOfQuaternionClasses
        down IsQuaternionClassB)
    (α β : A) (r : B)
    (hrU : down r = 0)
    (hβU : down (T.res β) = 0)
    (hcor : T.cor r = α) :
    let s := r + T.res β
    IsQuaternionClassB s ∧
      IsQuaternionClassB (s + T.res β) ∧
      T.cor s = α ∧
      T.cor (s + T.res β) = α ∧
      s + T.res β = r := by
  dsimp only
  have hresβ₂ : T.res β + T.res β = 0 := by
    rw [← map_add, hA₂ β, map_zero]
  have hsU : down (r + T.res β) = 0 := by
    rw [map_add, hrU, hβU, add_zero]
  have hswap : (r + T.res β) + T.res β = r := by
    calc
      (r + T.res β) + T.res β =
          r + (T.res β + T.res β) := by abel
      _ = r := by rw [hresβ₂, add_zero]
  have hsQuaternion : IsQuaternionClassB (r + T.res β) :=
    hKernelQuaternion (r + T.res β) hsU
  have hbackQuaternion :
      IsQuaternionClassB ((r + T.res β) + T.res β) := by
    rw [hswap]
    exact hKernelQuaternion r hrU
  have hsCor : T.cor (r + T.res β) = α := by
    rw [map_add, hcor, T.cor_res, hA₂ β, add_zero]
  have hbackCor :
      T.cor ((r + T.res β) + T.res β) = α := by
    rw [hswap, hcor]
  exact ⟨hsQuaternion, hbackQuaternion, hsCor, hbackCor, hswap⟩

/-- The preceding opposite-label correction is a genuine two-cycle when its
restricted label is nonzero. Nondegeneracy is deliberately an explicit
hypothesis rather than being inferred from the endpoint identities. -/
theorem oppositeLabelCorrection_forms_nondegenerateTwoCycle
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (hKernelQuaternion :
      LayerRestrictionKernelConsistsOfQuaternionClasses
        down IsQuaternionClassB)
    (α β : A) (r : B)
    (hrU : down r = 0)
    (hβU : down (T.res β) = 0)
    (hcor : T.cor r = α)
    (hβne : T.res β ≠ 0) :
    let s := r + T.res β
    IsQuaternionClassB s ∧
      IsQuaternionClassB (s + T.res β) ∧
      T.cor s = α ∧
      T.cor (s + T.res β) = α ∧
      s + T.res β = r ∧
      s ≠ r := by
  dsimp only
  rcases oppositeLabelCorrection_swaps_linkedLiftEndpoints
      hA₂ T down IsQuaternionClassB hKernelQuaternion
        α β r hrU hβU hcor with
    ⟨hsQuaternion, hbackQuaternion, hsCor, hbackCor, hswap⟩
  have hsne : r + T.res β ≠ r := by
    intro hs
    apply hβne
    simpa [add_assoc] using congrArg (fun x : B => -r + x) hs
  exact ⟨hsQuaternion, hbackQuaternion, hsCor, hbackCor, hswap, hsne⟩

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
