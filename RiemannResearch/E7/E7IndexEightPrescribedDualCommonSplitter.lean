/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightDualQuarticIncidence

/-!
# Prescribed dual common splitters and the remaining affine point

The Lam--Leep--Tignol construction can be oriented so that the nonnormal
quartic member of a dihedral dual pair splits two prescribed quaternion
classes.  Tignol's relative Brauer-kernel equality then places both classes
in the corestriction image of one upper quadratic-layer kernel.

This module records the exact formal consequence.  The prescribed incidence
makes the canonical corestriction fibre nonempty, but a crossed quaternion
rectangle exists exactly when one translated point of that fibre is
quaternion.  It does not assert that such a point exists.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w y

variable {A : Type u} {B : Type v} {C : Type w} {E : Type y}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E]

/-- One Tignol dual pair whose dual member splits both prescribed base
classes. -/
def HasPrescribedDualCommonSplitter
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (q₂ q₃ : A) : Prop :=
  DualQuarticRestrictionDetectsLayerCorestrictions T down dualDown ∧
    dualDown q₂ = 0 ∧ dualDown q₃ = 0

/-- The affine fibre of upper-layer-kernel classes with prescribed total
corestriction. -/
def CanonicalCrossedFibre
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (q₂ q₃ : A) : Set B :=
  {r | down r = 0 ∧ T.cor r = q₂ + q₃}

/-- A prescribed dual common splitter supplies separate upper-kernel
preimages of both prescribed base classes. -/
theorem exists_kernelPreimages_of_prescribedDualCommonSplitter
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (q₂ q₃ : A)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃) :
    (∃ s : B, down s = 0 ∧ T.cor s = q₂) ∧
      ∃ t : B, down t = 0 ∧ T.cor t = q₃ := by
  rcases h with ⟨hDual, hq₂, hq₃⟩
  have hq₂Image : q₂ ∈ AddSubgroup.map T.cor down.ker := by
    rw [hDual]
    simpa only [AddMonoidHom.mem_ker] using hq₂
  have hq₃Image : q₃ ∈ AddSubgroup.map T.cor down.ker := by
    rw [hDual]
    simpa only [AddMonoidHom.mem_ker] using hq₃
  rw [AddSubgroup.mem_map] at hq₂Image hq₃Image
  rcases hq₂Image with ⟨s, hs, hcorS⟩
  rcases hq₃Image with ⟨t, ht, hcorT⟩
  exact ⟨⟨s, hs, hcorS⟩, ⟨t, ht, hcorT⟩⟩

/-- The canonical total corestriction fibre is nonempty once both labels
come from the same upper-layer kernel. -/
theorem canonicalCrossedFibre_nonempty_of_prescribedDualCommonSplitter
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (q₂ q₃ : A)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃) :
    (CanonicalCrossedFibre T down q₂ q₃).Nonempty := by
  rcases exists_kernelPreimages_of_prescribedDualCommonSplitter
      T down dualDown q₂ q₃ h with
    ⟨⟨s, hs, hcorS⟩, ⟨t, ht, hcorT⟩⟩
  refine ⟨s + t, ?_, ?_⟩
  · rw [map_add, hs, ht, add_zero]
  · rw [map_add, hcorS, hcorT]

/-- Under prescribed dual incidence, the whole crossed-rectangle problem is
exactly the existence of one quaternion point in the translated canonical
affine fibre. -/
theorem hasCrossedQuaternionKernelRectangle_iff_exists_quaternionPoint
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (IsQuaternionClassB : B → Prop)
    (q₁ q₂ q₃ : A)
    (hFirst : T.res q₁ = 0)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃) :
    HasCrossedQuaternionKernelRectangle
        T down IsQuaternionClassB q₂ q₃ ↔
      ∃ r ∈ CanonicalCrossedFibre T down q₂ q₃,
        IsQuaternionClassB (r + T.res (q₁ + q₂)) := by
  rcases h with ⟨hDual, hq₂, hq₃⟩
  rw [hasCrossedQuaternionKernelRectangle_iff_dualConstituentSplitting_and_kernelComplement
    hA₂ hB₂ T down dualDown hDual IsQuaternionClassB
      q₁ q₂ q₃ hFirst]
  rw [and_iff_right hq₂]
  constructor
  · rintro ⟨r, hrDown, hrCor, hrQuaternion⟩
    exact ⟨r, ⟨hrDown, hrCor⟩, hrQuaternion⟩
  · rintro ⟨r, ⟨hrDown, hrCor⟩, hrQuaternion⟩
    exact ⟨r, hrDown, hrCor, hrQuaternion⟩

/-- The LLT--Tignol prescribed common splitter closes incidence and leaves
only the translated quaternion-point question. -/
theorem prescribedDualCommonSplitter_reduces_crossedRectangle_to_quaternionPoint
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (IsQuaternionClassB : B → Prop)
    (q₁ q₂ q₃ : A)
    (hFirst : T.res q₁ = 0)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃) :
    HasCrossedQuaternionKernelRectangle
        T down IsQuaternionClassB q₂ q₃ ↔
      ∃ r : B,
        down r = 0 ∧
          T.cor r = q₂ + q₃ ∧
          IsQuaternionClassB (r + T.res (q₁ + q₂)) := by
  constructor
  · intro hRectangle
    rcases
        (hasCrossedQuaternionKernelRectangle_iff_exists_quaternionPoint
          hA₂ hB₂ T down dualDown IsQuaternionClassB
            q₁ q₂ q₃ hFirst h).mp hRectangle with
      ⟨r, ⟨hrDown, hrCor⟩, hrQuaternion⟩
    exact ⟨r, hrDown, hrCor, hrQuaternion⟩
  · rintro ⟨r, hrDown, hrCor, hrQuaternion⟩
    apply
      (hasCrossedQuaternionKernelRectangle_iff_exists_quaternionPoint
        hA₂ hB₂ T down dualDown IsQuaternionClassB
          q₁ q₂ q₃ hFirst h).mpr
    exact ⟨r, ⟨hrDown, hrCor⟩, hrQuaternion⟩

/-- In the hard total-index-eight row, a successful crossed quaternion cannot
be split by a conjugation-stable quadratic layer.  Thus its common slot cannot
descend from the ground field. -/
theorem totalIndexEight_crossedQuaternion_has_no_stableSplittingLayer
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B)
    (split : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (hBGT : StableLayerQuaternionCorestrictionHasIndexAtMostTwo
      I T split IsQuaternionClassB)
    (q₁ q₂ q₃ : A)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8)
    (hFirst : I.index q₁ ≤ 2)
    (hOpposite : I.index (q₂ + q₃) ≤ 4)
    (s t : B)
    (hcorS : T.cor s = q₂)
    (hcorT : T.cor t = q₃)
    (hCrossQuaternion :
      IsQuaternionClassB (t + T.conjugate s))
    (hCrossSplit : split (t + T.conjugate s) = 0) :
    ¬ ConjugationPreservesLayerRestrictionKernel T split := by
  apply totalIndexEight_quaternionPreimageLayer_not_conjugationStable
    I T split IsQuaternionClassB hBGT
      q₁ (q₂ + q₃) (by simpa [add_assoc] using hTotal)
      hFirst hOpposite (t + T.conjugate s)
      hCrossQuaternion hCrossSplit
  rw [map_add, T.cor_conjugate, hcorT, hcorS, add_comm]

end RiemannResearch.E7.QuaternionTrialityPacket
