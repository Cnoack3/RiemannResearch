/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightCorestrictionAlignedLayerBridge

/-!
# Dual-quartic incidence for the hard E7 packet

Let M/F be the quadratic extension splitting the middle quaternion and let U/M
be a surviving nonnormal quadratic layer. In the intended field interpretation,

    A = Br₂(F), B = Br₂(M), C = Br₂(U), E = Br₂(check U).

Tignol, *Tores associés à une algèbre étale quartique*, Corollary 3.5 and
Example 5.3, applied to the dual quartic extension and combined with the
quaternion projection formula, identify

    cor_M/F (Br₂(U/M)) = Br₂(check U/F).

See <https://arxiv.org/html/1704.04072v1#S3.SS3> and
<https://arxiv.org/html/1704.04072v1#S5.SS3>. The predicate
DualQuarticRestrictionDetectsLayerCorestrictions records exactly that published
field-theoretic equality. Consequently the remaining labelled E7 alignment is

    q₁|_U = 0  and  (q₂ + q₃)|_(check U) = 0.

Under Arason exactness, this is also the vanishing of a canonical,
basepoint-independent class in Br₂(U) / res_U/F(Br₂(F)).

Lam--Leep--Tignol, *Biquaternion algebras and quartic extensions*, Theorem 3.9,
gives an explicit norm-polynomial description of the first condition. The
elementary polynomial identity used there is also kernel checked below:
<https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf>.

This is an exact conditional reduction. It does not construct the required
dual quartic pair or synchronize its two labelled splitting conditions.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w x y z

variable {A : Type u} {B : Type v} {C : Type w} {E : Type y}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E]

/-- Alignment separates into splitting of the first class and membership of
the opposite pairwise class in the corestriction image of the layer kernel. -/
theorem hasAlignedRelativeCorestrictionLayer_iff_kernel_and_corestrictionImage
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C)
    (q₁ q₂ q₃ : A) :
    HasAlignedRelativeCorestrictionLayer T down q₁ q₂ q₃ ↔
      T.res q₁ ∈ down.ker ∧
        q₂ + q₃ ∈ AddSubgroup.map T.cor down.ker := by
  constructor
  · rintro ⟨r, hq₁, hr, hcor⟩
    refine ⟨hq₁, ?_⟩
    rw [AddSubgroup.mem_map]
    exact ⟨r, hr, hcor⟩
  · rintro ⟨hq₁, himage⟩
    rw [AddSubgroup.mem_map] at himage
    rcases himage with ⟨r, hr, hcor⟩
    exact ⟨r, hq₁, hr, hcor⟩

/-- Relative to one prescribed-corestriction basepoint, alignment is exactly
one affine incidence with the range of ground-field restriction to U. -/
theorem hasAlignedRelativeCorestrictionLayer_iff_affineKernelIncidence
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (q₁ q₂ q₃ : A)
    (r₀ : B) (h₀ : T.cor r₀ = q₂ + q₃) :
    HasAlignedRelativeCorestrictionLayer T down q₁ q₂ q₃ ↔
      T.res q₁ ∈ down.ker ∧
        -down r₀ ∈ (down.comp T.res).range := by
  constructor
  · rintro ⟨r, hq₁, hr, hcor⟩
    refine ⟨hq₁, ?_⟩
    rcases
        (corestrictionFiber_iff_exists_restrictedTwist
          hA₂ T hexact (q₂ + q₃) r₀ h₀ r).mp hcor with
      ⟨γ, hγ⟩
    change ∃ γ : A, (down.comp T.res) γ = -down r₀
    refine ⟨γ, ?_⟩
    change down (T.res γ) = -down r₀
    rw [hγ, map_add] at hr
    exact eq_neg_of_add_eq_zero_right hr
  · rintro ⟨hq₁, hincidence⟩
    change ∃ γ : A, (down.comp T.res) γ = -down r₀ at hincidence
    rcases hincidence with ⟨γ, hγ⟩
    refine ⟨r₀ + T.res γ, hq₁, ?_, ?_⟩
    · rw [map_add]
      change down r₀ + (down.comp T.res) γ = 0
      rw [hγ, add_neg_cancel]
    · rw [map_add, h₀, T.cor_res, hA₂ γ, add_zero]

/-- The canonical upper-layer incidence cokernel. In the field model this is
Br₂(U) / res_U/F(Br₂(F)). -/
abbrev LayerIncidenceCokernel
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C) :=
  C ⧸ (down.comp T.res).range

/-- Restrict a prescribed-corestriction basepoint to U and take its class
modulo restrictions from F. -/
def alignedLayerIncidenceObstruction
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C)
    (r₀ : B) : LayerIncidenceCokernel T down :=
  QuotientAddGroup.mk' (down.comp T.res).range (down r₀)

/-- The incidence obstruction vanishes exactly when the restricted basepoint
can be corrected by a ground-field class. -/
theorem alignedLayerIncidenceObstruction_eq_zero_iff
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (r₀ : B) :
    alignedLayerIncidenceObstruction T down r₀ = 0 ↔
      down r₀ ∈ (down.comp T.res).range := by
  change (↑(down r₀) : C ⧸ (down.comp T.res).range) = 0 ↔ _
  exact QuotientAddGroup.eq_zero_iff
    (N := (down.comp T.res).range) (down r₀)

/-- An aligned layer exists exactly when it splits q₁ and the canonical
prescribed-corestriction incidence obstruction vanishes. -/
theorem hasAlignedRelativeCorestrictionLayer_iff_obstruction_eq_zero
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (q₁ q₂ q₃ : A)
    (r₀ : B) (h₀ : T.cor r₀ = q₂ + q₃) :
    HasAlignedRelativeCorestrictionLayer T down q₁ q₂ q₃ ↔
      T.res q₁ ∈ down.ker ∧
        alignedLayerIncidenceObstruction T down r₀ = 0 := by
  rw [hasAlignedRelativeCorestrictionLayer_iff_affineKernelIncidence
    hA₂ T down hexact q₁ q₂ q₃ r₀ h₀]
  rw [alignedLayerIncidenceObstruction_eq_zero_iff]
  simp only [neg_mem_iff]

/-- The incidence obstruction is independent of the chosen point in the
prescribed-corestriction fibre. -/
theorem alignedLayerIncidenceObstruction_eq_of_same_corestriction
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (α : A) (r₀ r₁ : B)
    (h₀ : T.cor r₀ = α) (h₁ : T.cor r₁ = α) :
    alignedLayerIncidenceObstruction T down r₀ =
      alignedLayerIncidenceObstruction T down r₁ := by
  rcases
      (corestrictionFiber_iff_exists_restrictedTwist
        hA₂ T hexact α r₀ h₀ r₁).mp h₁ with
    ⟨γ, hγ⟩
  rw [hγ]
  change
    QuotientAddGroup.mk' (down.comp T.res).range (down r₀) =
      QuotientAddGroup.mk' (down.comp T.res).range
        (down (r₀ + T.res γ))
  rw [map_add, map_add]
  have hz :
      QuotientAddGroup.mk' (down.comp T.res).range
          (down (T.res γ)) = 0 := by
    change (↑(down (T.res γ)) :
      C ⧸ (down.comp T.res).range) = 0
    exact
      (QuotientAddGroup.eq_zero_iff
        (N := (down.comp T.res).range) (down (T.res γ))).2 ⟨γ, rfl⟩
  rw [hz, add_zero]

/-- The corestriction image of the layer kernel is unchanged under quadratic
conjugation of the upper layer. -/
theorem conjugateLayer_corestrictionImage_eq
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C) :
    AddSubgroup.map T.cor (conjugateLayerRestriction T down).ker =
      AddSubgroup.map T.cor down.ker := by
  ext a
  constructor
  · intro ha
    rw [AddSubgroup.mem_map] at ha ⊢
    rcases ha with ⟨r, hr, hcor⟩
    refine ⟨T.conjugate r, ?_, ?_⟩
    · exact hr
    · rw [T.cor_conjugate]
      exact hcor
  · intro ha
    rw [AddSubgroup.mem_map] at ha ⊢
    rcases ha with ⟨r, hr, hcor⟩
    refine ⟨T.conjugate r, ?_, ?_⟩
    · simpa [conjugateLayerRestriction,
        T.conjugate_involutive] using hr
    · rw [T.cor_conjugate]
      exact hcor

/-- The subgroup of base classes split by U is unchanged under quadratic
conjugation of U. -/
theorem conjugateLayer_baseRestrictionKernel_eq
    (T : QuadraticBrauerTransferModel A B) (down : B →+ C) :
    AddSubgroup.comap T.res (conjugateLayerRestriction T down).ker =
      AddSubgroup.comap T.res down.ker := by
  ext a
  simp only [AddSubgroup.mem_comap, AddMonoidHom.mem_ker,
    conjugateLayerRestriction, AddMonoidHom.coe_comp,
    Function.comp_apply, T.conjugate_res]

/-- Tignol's dual-quartic relative-Brauer equality: corestrictions of classes
split by U/M are precisely the base classes split by check U/F. -/
def DualQuarticRestrictionDetectsLayerCorestrictions
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E) : Prop :=
  AddSubgroup.map T.cor down.ker = dualDown.ker

/-- Dual-quartic detection is invariant under conjugating the upper layer. -/
theorem dualQuarticRestrictionDetectsLayerCorestrictions_conjugate_iff
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E) :
    DualQuarticRestrictionDetectsLayerCorestrictions
        T (conjugateLayerRestriction T down) dualDown ↔
      DualQuarticRestrictionDetectsLayerCorestrictions T down dualDown := by
  unfold DualQuarticRestrictionDetectsLayerCorestrictions
  rw [conjugateLayer_corestrictionImage_eq]

/-- The aligned-layer search is exactly a dual-quartic incidence: U splits q₁
and check U splits q₂ + q₃. -/
theorem hasAlignedRelativeCorestrictionLayer_iff_dualQuarticSplitting
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (hDual : DualQuarticRestrictionDetectsLayerCorestrictions
      T down dualDown)
    (q₁ q₂ q₃ : A) :
    HasAlignedRelativeCorestrictionLayer T down q₁ q₂ q₃ ↔
      down (T.res q₁) = 0 ∧ dualDown (q₂ + q₃) = 0 := by
  rw [hasAlignedRelativeCorestrictionLayer_iff_kernel_and_corestrictionImage]
  change AddSubgroup.map T.cor down.ker = dualDown.ker at hDual
  rw [hDual]
  simp only [AddMonoidHom.mem_ker]

/-- Across any indexed family of dual quartic pairs, the existential
relative-corestriction witness can be eliminated uniformly. The remaining
choice is exactly a pair whose two opposite quartics split the two labels. -/
theorem exists_alignedRelativeCorestrictionLayer_iff_exists_dualQuarticSplitting
    {ι : Type z}
    (T : QuadraticBrauerTransferModel A B)
    (down : ι → B →+ C) (dualDown : ι → A →+ E)
    (hDual : ∀ i, DualQuarticRestrictionDetectsLayerCorestrictions
      T (down i) (dualDown i))
    (q₁ q₂ q₃ : A) :
    (∃ i, HasAlignedRelativeCorestrictionLayer T (down i) q₁ q₂ q₃) ↔
      ∃ i, down i (T.res q₁) = 0 ∧ dualDown i (q₂ + q₃) = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i,
      (hasAlignedRelativeCorestrictionLayer_iff_dualQuarticSplitting
        T (down i) (dualDown i) (hDual i) q₁ q₂ q₃).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i,
      (hasAlignedRelativeCorestrictionLayer_iff_dualQuarticSplitting
        T (down i) (dualDown i) (hDual i) q₁ q₂ q₃).mpr hi⟩
/-- Dual restriction detects the vanishing of the canonical incidence
obstruction independently of the chosen corestriction basepoint. -/
theorem alignedLayerIncidenceObstruction_eq_zero_iff_dualQuarticSplitting
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (hDual : DualQuarticRestrictionDetectsLayerCorestrictions
      T down dualDown)
    (α : A) (r₀ : B) (h₀ : T.cor r₀ = α) :
    alignedLayerIncidenceObstruction T down r₀ = 0 ↔
      dualDown α = 0 := by
  have hObstruction :=
    hasAlignedRelativeCorestrictionLayer_iff_obstruction_eq_zero
      hA₂ T down hexact (0 : A) α 0 r₀ (by simpa using h₀)
  have hDualSplitting :=
    hasAlignedRelativeCorestrictionLayer_iff_dualQuarticSplitting
      T down dualDown hDual (0 : A) α 0
  exact (by simpa using hObstruction.symm.trans hDualSplitting)

/-- If a class of index at most two plus a class of index at most four
has sum of index eight, the second class has index exactly four. In the hard E7
row this shows that the opposite pair q₂ + q₃ is a division biquaternion. -/
theorem oppositePairIndex_eq_four_of_totalIndexEight
    (I : BrauerIndexModel A)
    (q₁ α : A)
    (hTotal : I.index (q₁ + α) = 8)
    (hFirst : I.index q₁ ≤ 2)
    (hOpposite : I.index α ≤ 4) :
    I.index α = 4 := by
  have hEightLeProduct : 8 ≤ I.index q₁ * I.index α := by
    rw [← hTotal]
    exact I.index_add_le_mul q₁ α
  have hProductUpper : I.index q₁ * I.index α ≤
      2 * I.index α :=
    Nat.mul_le_mul_right (I.index α) hFirst
  have hEightLeTwice : 8 ≤ 2 * I.index α :=
    le_trans hEightLeProduct hProductUpper
  omega

/-- The exact field input extracted from Becher--Grenier-Boley--Tignol,
Theorem 0.1: a quaternion split by a conjugation-stable quadratic layer has
corestriction of index at most two.

See <https://arxiv.org/pdf/1610.06096>. -/
def StableLayerQuaternionCorestrictionHasIndexAtMostTwo
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (IsQuaternionClassB : B → Prop) : Prop :=
  ∀ r : B, IsQuaternionClassB r → down r = 0 →
    ConjugationPreservesLayerRestrictionKernel T down →
      I.index (T.cor r) ≤ 2

/-- A quaternion with division-biquaternion corestriction cannot be split by
a conjugation-stable upper quadratic layer. -/
theorem corestrictionIndexFour_quaternionSplittingLayer_not_conjugationStable
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (IsQuaternionClassB : B → Prop)
    (hBGT : StableLayerQuaternionCorestrictionHasIndexAtMostTwo
      I T down IsQuaternionClassB)
    (r : B) (hrQuaternion : IsQuaternionClassB r)
    (hrSplit : down r = 0)
    (hCorIndex : I.index (T.cor r) = 4) :
    ¬ ConjugationPreservesLayerRestrictionKernel T down := by
  intro hstable
  have hle := hBGT r hrQuaternion hrSplit hstable
  omega

/-- Automatic nonnormality before alignment: in the total-index-eight row,
every quadratic splitting layer of every quaternion preimage of the opposite
pair is non-stable. No hypothesis that the layer also splits q₁ is needed. -/
theorem totalIndexEight_quaternionPreimageLayer_not_conjugationStable
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (IsQuaternionClassB : B → Prop)
    (hBGT : StableLayerQuaternionCorestrictionHasIndexAtMostTwo
      I T down IsQuaternionClassB)
    (q₁ α : A)
    (hTotal : I.index (q₁ + α) = 8)
    (hFirst : I.index q₁ ≤ 2)
    (hOpposite : I.index α ≤ 4)
    (r : B) (hrQuaternion : IsQuaternionClassB r)
    (hrSplit : down r = 0)
    (hcor : T.cor r = α) :
    ¬ ConjugationPreservesLayerRestrictionKernel T down := by
  have hAlphaIndex :=
    oppositePairIndex_eq_four_of_totalIndexEight
      I q₁ α hTotal hFirst hOpposite
  apply corestrictionIndexFour_quaternionSplittingLayer_not_conjugationStable
    I T down IsQuaternionClassB hBGT r hrQuaternion hrSplit
  rwa [hcor]
/-- The norm-polynomial identity behind the explicit LLT parametrization. If
n = b² - 4ac², the left side is the norm of 2ae + b + √n from F(√n). -/
theorem dualQuartic_normPolynomial_identity
    {F : Type z} [CommRing F] (a b c e : F) :
    (2 * a * e + b) ^ 2 - (b ^ 2 - 4 * a * c ^ 2) =
      4 * a * (a * e ^ 2 + b * e + c ^ 2) := by
  ring

/-- Vanishing of the canonical layer obstruction implies E7 packet
effectivity through the existing aligned-layer bridge. -/
theorem BoundaryRealization.isEffective_of_vanishingAlignedLayerObstruction
    (hA₂ : IsExponentTwo A)
    (R : BoundaryRealization.{u, x} A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (IsQuaternionClassB : B → Prop)
    (hKernelQuaternion :
      LayerRestrictionKernelConsistsOfQuaternionClasses down IsQuaternionClassB)
    (Disc : CommonDiscriminantSumConstructor R T IsQuaternionClassB)
    (q₁ q₂ q₃ : A) (r₀ : B)
    (hMiddle : T.res q₂ = 0)
    (h₀ : T.cor r₀ = q₂ + q₃)
    (hFirst : T.res q₁ ∈ down.ker)
    (hObstruction :
      alignedLayerIncidenceObstruction T down r₀ = 0) :
    R.IsEffective (BrauerPacket.ofTriple q₁ q₂ q₃) := by
  have hAligned :=
    (hasAlignedRelativeCorestrictionLayer_iff_obstruction_eq_zero
      hA₂ T down hexact q₁ q₂ q₃ r₀ h₀).mpr ⟨hFirst, hObstruction⟩
  exact R.isEffective_of_alignedLayerForTriple
    hA₂ T down IsQuaternionClassB hKernelQuaternion Disc
      q₁ q₂ q₃ hMiddle hAligned

/-- Opposite labelled splitting in a dual nonnormal quartic pair implies E7
packet effectivity, subject to the isolated quaternion-kernel and
common-discriminant inputs. -/
theorem BoundaryRealization.isEffective_of_dualQuarticSplitting
    (hA₂ : IsExponentTwo A)
    (R : BoundaryRealization.{u, x} A)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (hDual : DualQuarticRestrictionDetectsLayerCorestrictions
      T down dualDown)
    (IsQuaternionClassB : B → Prop)
    (hKernelQuaternion :
      LayerRestrictionKernelConsistsOfQuaternionClasses down IsQuaternionClassB)
    (Disc : CommonDiscriminantSumConstructor R T IsQuaternionClassB)
    (q₁ q₂ q₃ : A)
    (hMiddle : T.res q₂ = 0)
    (hFirst : down (T.res q₁) = 0)
    (hOpposite : dualDown (q₂ + q₃) = 0) :
    R.IsEffective (BrauerPacket.ofTriple q₁ q₂ q₃) := by
  have hAligned :=
    (hasAlignedRelativeCorestrictionLayer_iff_dualQuarticSplitting
      T down dualDown hDual q₁ q₂ q₃).mpr ⟨hFirst, hOpposite⟩
  exact R.isEffective_of_alignedLayerForTriple
    hA₂ T down IsQuaternionClassB hKernelQuaternion Disc
      q₁ q₂ q₃ hMiddle hAligned

end RiemannResearch.E7.QuaternionTrialityPacket
