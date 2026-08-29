/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib
import RiemannResearch.E7.E7BoundaryEffectivity
import RiemannResearch.E7.D6A1FiniteCertificate

/-!
# The exact index-eight boundary in the remaining type-E7 case

This module records two reductions at the E7 effectivity boundary.

First, the four-quaternion completion route is equivalent to finding another
quaternion representative of the same labelled pairwise-sum packet whose total
class is quaternion.

Second, the standard tensor-product index inequality implies that three
quaternion classes with total index eight have trialitarian packet index
`(4,4,4)`. This row is absent from the isotropic triality table over fields with
`I_q^3 = 0`. Therefore that table constrains an already constructed hard
realization; it cannot provide the missing effectivity theorem.

No realization theorem is assumed here.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

open RiemannResearch.E7.D6A1FiniteCertificate

universe u

variable {A : Type u} [AddCommGroup A]

/-- A target packet has a quaternion representative with quaternion total when
one can change the three quaternion inputs without changing their packet and
make the total of the new triple quaternion as well. -/
def HasQuaternionRepresentativeWithQuaternionTotal
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) : Prop :=
  ∃ q₁' q₂' q₃' : A,
    IsQuaternionClass q₁' ∧
      IsQuaternionClass q₂' ∧
      IsQuaternionClass q₃' ∧
      IsQuaternionClass (q₁' + q₂' + q₃') ∧
      BrauerPacket.ofTriple q₁' q₂' q₃' =
        BrauerPacket.ofTriple q₁ q₂ q₃

/-- Four-quaternion completion is equivalent to finding, in the diagonal fibre
of the target packet, a quaternion triple whose total class is quaternion. -/
theorem hasQuaternionCompletion_iff_representativeWithQuaternionTotal
    (h₂ : IsExponentTwo A)
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) :
    HasQuaternionCompletion IsQuaternionClass q₁ q₂ q₃ ↔
      HasQuaternionRepresentativeWithQuaternionTotal
        IsQuaternionClass q₁ q₂ q₃ := by
  constructor
  · rintro ⟨r, hr, hp₂, hp₃, hp₄⟩
    refine ⟨r, r + q₁ + q₂, r + q₁ + q₃,
      hr, hp₃, hp₄, ?_, ?_⟩
    · have h :
          r + (r + q₁ + q₂) + (r + q₁ + q₃) = r + q₂ + q₃ := by
        calc
          r + (r + q₁ + q₂) + (r + q₁ + q₃) =
              (r + r) + r + (q₁ + q₁) + q₂ + q₃ := by abel
          _ = r + q₂ + q₃ := by rw [h₂ r, h₂ q₁]; simp
      rw [h]
      exact hp₂
    · apply BrauerPacket.ext
      · change (r + q₁ + q₂) + (r + q₁ + q₃) = q₂ + q₃
        calc
          (r + q₁ + q₂) + (r + q₁ + q₃) =
              (r + r) + (q₁ + q₁) + q₂ + q₃ := by abel
          _ = q₂ + q₃ := by rw [h₂ r, h₂ q₁]; simp
      · change r + (r + q₁ + q₂) = q₁ + q₂
        calc
          r + (r + q₁ + q₂) = (r + r) + q₁ + q₂ := by abel
          _ = q₁ + q₂ := by rw [h₂ r]; simp
      · change r + (r + q₁ + q₃) = q₁ + q₃
        calc
          r + (r + q₁ + q₃) = (r + r) + q₁ + q₃ := by abel
          _ = q₁ + q₃ := by rw [h₂ r]; simp
  · rintro ⟨q₁', q₂', q₃', hq₁', hq₂', hq₃', htotal', hpacket⟩
    rcases (BrauerPacket.ofTriple_eq_iff_diagonal h₂
      q₁' q₂' q₃' q₁ q₂ q₃).1 hpacket with
      ⟨s, hq₁, hq₂, hq₃⟩
    let r : A := q₁' + q₂' + q₃'
    refine ⟨r, htotal', ?_, ?_, ?_⟩
    · have h : r + q₂ + q₃ = q₁' := by
        dsimp [r]
        rw [hq₂, hq₃]
        calc
          q₁' + q₂' + q₃' + (q₂' + s) + (q₃' + s) =
              q₁' + (q₂' + q₂') + (q₃' + q₃') + (s + s) := by abel
          _ = q₁' := by rw [h₂ q₂', h₂ q₃', h₂ s]; simp
      rw [h]
      exact hq₁'
    · have h : r + q₁ + q₂ = q₃' := by
        dsimp [r]
        rw [hq₁, hq₂]
        calc
          q₁' + q₂' + q₃' + (q₁' + s) + (q₂' + s) =
              (q₁' + q₁') + (q₂' + q₂') + q₃' + (s + s) := by abel
          _ = q₃' := by rw [h₂ q₁', h₂ q₂', h₂ s]; simp
      rw [h]
      exact hq₃'
    · have h : r + q₁ + q₃ = q₂' := by
        dsimp [r]
        rw [hq₁, hq₃]
        calc
          q₁' + q₂' + q₃' + (q₁' + s) + (q₃' + s) =
              (q₁' + q₁') + q₂' + (q₃' + q₃') + (s + s) := by abel
          _ = q₂' := by rw [h₂ q₁', h₂ q₃', h₂ s]; simp
      rw [h]
      exact hq₂'

/-- A packet has a split labelled slot when one of its Brauer classes is zero. -/
def BrauerPacket.HasSplitSlot (P : BrauerPacket A) : Prop :=
  P.underlying = 0 ∨ P.cliffordPlus = 0 ∨ P.cliffordMinus = 0

/-- A split labelled slot gives a four-quaternion completion. -/
theorem hasQuaternionCompletion_of_splitSlot
    (h₂ : IsExponentTwo A)
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A)
    (hq₁ : IsQuaternionClass q₁)
    (hq₂ : IsQuaternionClass q₂)
    (hq₃ : IsQuaternionClass q₃)
    (hSplit : (BrauerPacket.ofTriple q₁ q₂ q₃).HasSplitSlot) :
    HasQuaternionCompletion IsQuaternionClass q₁ q₂ q₃ := by
  change q₂ + q₃ = 0 ∨ q₁ + q₂ = 0 ∨ q₁ + q₃ = 0 at hSplit
  apply hasQuaternionCompletion_of_total h₂ IsQuaternionClass
    q₁ q₂ q₃ hq₁ hq₂ hq₃
  rcases hSplit with h₂₃ | h₁₂ | h₁₃
  · have h : q₁ + q₂ + q₃ = q₁ := by
      calc
        q₁ + q₂ + q₃ = q₁ + (q₂ + q₃) := by abel
        _ = q₁ := by rw [h₂₃, add_zero]
    rwa [h]
  · have h : q₁ + q₂ + q₃ = q₃ := by
      calc
        q₁ + q₂ + q₃ = (q₁ + q₂) + q₃ := rfl
        _ = q₃ := by rw [h₁₂, zero_add]
    rwa [h]
  · have h : q₁ + q₂ + q₃ = q₂ := by
      calc
        q₁ + q₂ + q₃ = (q₁ + q₃) + q₂ := by abel
        _ = q₂ := by rw [h₁₃, zero_add]
    rwa [h]

/-- Minimal numerical properties of the Schur index used below. Addition
models tensor product in the two-primary Brauer group. -/
structure BrauerIndexModel (A : Type u) [AddCommGroup A] where
  index : A → ℕ
  index_zero : index 0 = 1
  index_add_le_mul : ∀ x y : A, index (x + y) ≤ index x * index y

/-- A designated quaternion-class predicate has Schur index at most two. -/
def QuaternionClassesHaveIndexAtMostTwo
    (I : BrauerIndexModel A) (IsQuaternionClass : A → Prop) : Prop :=
  ∀ q : A, IsQuaternionClass q → I.index q ≤ 2

private theorem pair_index_four_of_total_index_eight
    (I : BrauerIndexModel A)
    (IsQuaternionClass : A → Prop)
    (hQuaternion : QuaternionClassesHaveIndexAtMostTwo I IsQuaternionClass)
    (a b c : A)
    (ha : IsQuaternionClass a)
    (hb : IsQuaternionClass b)
    (hc : IsQuaternionClass c)
    (hTotal : I.index (a + b + c) = 8) :
    I.index (b + c) = 4 := by
  have haIndex : I.index a ≤ 2 := hQuaternion a ha
  have hbIndex : I.index b ≤ 2 := hQuaternion b hb
  have hcIndex : I.index c ≤ 2 := hQuaternion c hc
  have hPairUpper : I.index (b + c) ≤ 4 := by
    calc
      I.index (b + c) ≤ I.index b * I.index c := I.index_add_le_mul b c
      _ ≤ 2 * 2 := Nat.mul_le_mul hbIndex hcIndex
      _ = 4 := by norm_num
  have hTotalAssoc : I.index (a + (b + c)) = 8 := by
    simpa [add_assoc] using hTotal
  have hEightLeProduct : 8 ≤ I.index a * I.index (b + c) := by
    rw [← hTotalAssoc]
    exact I.index_add_le_mul a (b + c)
  have hProductUpper : I.index a * I.index (b + c) ≤
      2 * I.index (b + c) :=
    Nat.mul_le_mul_right (I.index (b + c)) haIndex
  have hEightLeTwice : 8 ≤ 2 * I.index (b + c) :=
    le_trans hEightLeProduct hProductUpper
  omega

/-- Total index eight forces all three packet indices to equal four. -/
theorem total_index_eight_forces_packet_index_four
    (I : BrauerIndexModel A)
    (IsQuaternionClass : A → Prop)
    (hQuaternion : QuaternionClassesHaveIndexAtMostTwo I IsQuaternionClass)
    (q₁ q₂ q₃ : A)
    (hq₁ : IsQuaternionClass q₁)
    (hq₂ : IsQuaternionClass q₂)
    (hq₃ : IsQuaternionClass q₃)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8) :
    I.index (BrauerPacket.ofTriple q₁ q₂ q₃).underlying = 4 ∧
      I.index (BrauerPacket.ofTriple q₁ q₂ q₃).cliffordPlus = 4 ∧
      I.index (BrauerPacket.ofTriple q₁ q₂ q₃).cliffordMinus = 4 := by
  have h₂₃ := pair_index_four_of_total_index_eight
    I IsQuaternionClass hQuaternion q₁ q₂ q₃ hq₁ hq₂ hq₃ hTotal
  have hTotal312 : I.index (q₃ + q₁ + q₂) = 8 := by
    rw [show q₃ + q₁ + q₂ = q₁ + q₂ + q₃ by abel]
    exact hTotal
  have h₁₂ := pair_index_four_of_total_index_eight
    I IsQuaternionClass hQuaternion q₃ q₁ q₂ hq₃ hq₁ hq₂ hTotal312
  have hTotal213 : I.index (q₂ + q₁ + q₃) = 8 := by
    rw [show q₂ + q₁ + q₃ = q₁ + q₂ + q₃ by abel]
    exact hTotal
  have h₁₃ := pair_index_four_of_total_index_eight
    I IsQuaternionClass hQuaternion q₂ q₁ q₃ hq₂ hq₁ hq₃ hTotal213
  exact ⟨h₂₃, h₁₂, h₁₃⟩

/-- The hard index-eight packet has no split labelled slot. -/
theorem total_index_eight_packet_has_no_splitSlot
    (I : BrauerIndexModel A)
    (IsQuaternionClass : A → Prop)
    (hQuaternion : QuaternionClassesHaveIndexAtMostTwo I IsQuaternionClass)
    (q₁ q₂ q₃ : A)
    (hq₁ : IsQuaternionClass q₁)
    (hq₂ : IsQuaternionClass q₂)
    (hq₃ : IsQuaternionClass q₃)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8) :
    ¬ (BrauerPacket.ofTriple q₁ q₂ q₃).HasSplitSlot := by
  rcases total_index_eight_forces_packet_index_four
      I IsQuaternionClass hQuaternion q₁ q₂ q₃ hq₁ hq₂ hq₃ hTotal with
    ⟨hUnderlying, hPlus, hMinus⟩
  rintro (hZero | hZero | hZero)
  · rw [hZero, I.index_zero] at hUnderlying
    norm_num at hUnderlying
  · rw [hZero, I.index_zero] at hPlus
    norm_num at hPlus
  · rw [hZero, I.index_zero] at hMinus
    norm_num at hMinus

/-- The all-index-four row is excluded from the isotropic triality table. -/
theorem not_allowedTrialitarianIndexTriple_four_four_four :
    ¬ AllowedTrialitarianIndexTriple 4 4 4 := by
  norm_num [AllowedTrialitarianIndexTriple]

/-- An index-eight quaternion triple has a packet outside the isotropic table. -/
theorem total_index_eight_packet_not_allowed
    (I : BrauerIndexModel A)
    (IsQuaternionClass : A → Prop)
    (hQuaternion : QuaternionClassesHaveIndexAtMostTwo I IsQuaternionClass)
    (q₁ q₂ q₃ : A)
    (hq₁ : IsQuaternionClass q₁)
    (hq₂ : IsQuaternionClass q₂)
    (hq₃ : IsQuaternionClass q₃)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8) :
    ¬ AllowedTrialitarianIndexTriple
      (I.index (BrauerPacket.ofTriple q₁ q₂ q₃).underlying)
      (I.index (BrauerPacket.ofTriple q₁ q₂ q₃).cliffordPlus)
      (I.index (BrauerPacket.ofTriple q₁ q₂ q₃).cliffordMinus) := by
  rcases total_index_eight_forces_packet_index_four
      I IsQuaternionClass hQuaternion q₁ q₂ q₃ hq₁ hq₂ hq₃ hTotal with
    ⟨hUnderlying, hPlus, hMinus⟩
  rw [hUnderlying, hPlus, hMinus]
  exact not_allowedTrialitarianIndexTriple_four_four_four

/-- Any actual realization of the hard packet is anisotropic, provided
isotropic realizations obey the classified trialitarian index table. -/
theorem realization_of_total_index_eight_is_anisotropic
    (I : BrauerIndexModel A)
    (IsQuaternionClass : A → Prop)
    (hQuaternion : QuaternionClassesHaveIndexAtMostTwo I IsQuaternionClass)
    (C : BoundaryRealization A)
    (IsIsotropic : C.Object → Prop)
    (isotropic_indices_allowed : ∀ X : C.Object,
      IsIsotropic X →
        AllowedTrialitarianIndexTriple
          (I.index (C.packet X).underlying)
          (I.index (C.packet X).cliffordPlus)
          (I.index (C.packet X).cliffordMinus))
    (q₁ q₂ q₃ : A)
    (hq₁ : IsQuaternionClass q₁)
    (hq₂ : IsQuaternionClass q₂)
    (hq₃ : IsQuaternionClass q₃)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8)
    (X : C.Object)
    (hPacket : C.packet X = BrauerPacket.ofTriple q₁ q₂ q₃) :
    ¬ IsIsotropic X := by
  intro hIso
  have hAllowed := isotropic_indices_allowed X hIso
  rw [hPacket] at hAllowed
  exact (total_index_eight_packet_not_allowed
    I IsQuaternionClass hQuaternion q₁ q₂ q₃
      hq₁ hq₂ hq₃ hTotal) hAllowed

end RiemannResearch.E7.QuaternionTrialityPacket
