/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightCorestrictionHardOrbit

/-!
# Excluding conjugation-stable aligned layers in the hard E7 reduction

The corrected nested-quadratic target asks for a quadratic layer `U/M`
which both splits `q₁_M` and supports a relative-corestriction witness for
`q₂ + q₃`. This module proves that such a layer cannot be stable under the
nontrivial conjugation of `M/F` in the hard total-index-eight row.

The proof uses only the transfer identity

```text
res_M(cor_M/F(r)) = r + conjugate(r).
```

If restriction from `M` to `U` has conjugation-stable kernel and kills
`r`, it also kills `conjugate(r)), hence kills the restriction of
`cor(r)`. Therefore an aligned layer, together with `q₂_M = 0), splits
all three classes `q₁`, `q₂`, and `q₃`, and hence their total.

In the intended field model, conjugation-stability of the restriction kernel
is supplied when the nontrivial automorphism of `M/F` extends to `U);
in particular this holds when the degree-four extension `U/F` is Galois.
But a degree-four field cannot split an index-eight class, since the index
divides the degree of every finite splitting field; see the Stacks Project,
Lemma 11.8.4 (tag 074X): <https://stacks.math.columbia.edu/tag/074X>.

Thus a successful labelled layer must be genuinely nonnormal over `F`.
In a dihedral quartic framework this excludes the conjugation-stable/Galois
quartic layer and leaves only the nonnormal conjugate layers as candidates.
Lam--Leep--Tignol, *Biquaternion algebras and quartic extensions*, Publ.
Math. IHES 77 (1993), Proposition 3.3 and Theorems 5.10 and 5.12, supports
the dihedral and corestriction terminology:
<https://www.numdam.org/articles/10.1007/BF02699188/>.

The field-theoretic providers are explicit predicates below; this module does
not formalize fields, extension degrees, or the existence of an aligned layer.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Restriction from the quadratic layer `M` to a further layer `U` has
kernel preserved by the nontrivial conjugation of `M/F`.

For fields this is implied by an extension of the conjugation automorphism
from `M` to `U`, as happens when `U/F` is Galois. -/
def ConjugationPreservesLayerRestrictionKernel
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C) : Prop :=
  ∀ r : B, down r = 0 → down (T.conjugate r) = 0

/-- The numerical splitting-field property for the degree-four tower
`F ⊆ M ⊆ U`: every base class killed over `U` has index at most four. -/
def DegreeFourTowerRestrictionKernelHasIndexAtMostFour
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C) : Prop :=
  ∀ a : A, down (T.res a) = 0 → I.index a ≤ 4

/-- The labelled nested-layer target: `U` splits `q₁_M`, and a class
split by `U/M` has corestriction `q₂ + q₃`. -/
def HasAlignedRelativeCorestrictionLayer
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C)
    (q₁ q₂ q₃ : A) : Prop :=
  ∃ r : B,
    down (T.res q₁) = 0 ∧
    down r = 0 ∧
    T.cor r = q₂ + q₃

/-- A conjugation-stable layer which splits a relative class also splits the
base restriction of its corestriction. -/
theorem layerRestriction_res_corestriction_eq_zero
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C)
    (hstable : ConjugationPreservesLayerRestrictionKernel T down)
    (r : B) (hr : down r = 0) :
    down (T.res (T.cor r)) = 0 := by
  rw [T.res_cor, map_add, hr, hstable r hr, add_zero]

/-- If the middle quaternion is already split over `M`, every aligned
conjugation-stable layer splits the total class `q₁ + q₂ + q₃` over `U`. -/
theorem alignedLayer_splits_total_of_conjugationStable
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C)
    (hstable : ConjugationPreservesLayerRestrictionKernel T down)
    (q₁ q₂ q₃ : A) (hMiddle : T.res q₂ = 0)
    (hAligned : HasAlignedRelativeCorestrictionLayer
      T down q₁ q₂ q₃) :
    down (T.res (q₁ + q₂ + q₃)) = 0 := by
  rcases hAligned with ⟨r, hq₁U, hrU, hcor⟩
  have hαU : down (T.res (q₂ + q₃)) = 0 := by
    rw [← hcor]
    exact layerRestriction_res_corestriction_eq_zero
      T down hstable r hrU
  have hq₂U : down (T.res q₂) = 0 := by
    rw [hMiddle, map_zero]
  have hαU' : down (T.res q₂) + down (T.res q₃) = 0 := by
    simpa only [map_add] using hαU
  have hq₃U : down (T.res q₃) = 0 := by
    simpa only [hq₂U, zero_add] using hαU'
  calc
    down (T.res (q₁ + q₂ + q₃)) =
        down (T.res q₁) + down (T.res q₂) +
          down (T.res q₃) := by
            simp only [map_add]
    _ = 0 := by rw [hq₁U, hq₂U, hq₃U]; simp

/-- A conjugation-stable aligned layer is impossible for a total-index-eight
class when the degree-four splitting bound holds. -/
theorem totalIndexEight_excludes_conjugationStable_alignedLayer
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C)
    (hstable : ConjugationPreservesLayerRestrictionKernel T down)
    (hDegreeFour :
      DegreeFourTowerRestrictionKernelHasIndexAtMostFour I T down)
    (q₁ q₂ q₃ : A)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8)
    (hMiddle : T.res q₂ = 0) :
    ¬ HasAlignedRelativeCorestrictionLayer T down q₁ q₂ q₃ := by
  intro hAligned
  have htotalU := alignedLayer_splits_total_of_conjugationStable
    T down hstable q₁ q₂ q₃ hMiddle hAligned
  have hle := hDegreeFour (q₁ + q₂ + q₃) htotalU
  omega

/-- Equivalently, every aligned layer for a hard total-index-eight packet must
have restriction kernel not preserved by the quadratic conjugation. In the
field interpretation, a successful quartic layer cannot be Galois over the
base field. -/
theorem totalIndexEight_alignedLayer_not_conjugationStable
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C)
    (hDegreeFour :
      DegreeFourTowerRestrictionKernelHasIndexAtMostFour I T down)
    (q₁ q₂ q₃ : A)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8)
    (hMiddle : T.res q₂ = 0)
    (hAligned : HasAlignedRelativeCorestrictionLayer
      T down q₁ q₂ q₃) :
    ¬ ConjugationPreservesLayerRestrictionKernel T down := by
  intro hstable
  exact totalIndexEight_excludes_conjugationStable_alignedLayer
    I T down hstable hDegreeFour q₁ q₂ q₃ hTotal hMiddle hAligned

end RiemannResearch.E7.QuaternionTrialityPacket
