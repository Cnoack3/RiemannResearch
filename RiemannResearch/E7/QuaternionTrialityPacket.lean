/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Abel

/-!
# The Brauer packet behind the remaining type-E7 bridge

For three quaternion Brauer classes `q₁`, `q₂`, and `q₃`, the remaining E7
construction asks for a degree-eight algebra with quadratic pair whose three
trialitarian Brauer classes are

* `q₂ + q₃`,
* `q₁ + q₂`, and
* `q₁ + q₃`.

This module isolates the exact exponent-two arithmetic of that packet.  It
also proves that the four-quaternion orthogonal-sum construction is equivalent,
at the level of Brauer classes, to one explicit quaternion-completion problem.
No existence of that completion is assumed or asserted.

The published input motivating the four-class presentation is Proposition 5.4
of A. Dolphin and A. Quéguiner-Mathieu, *The canonical quadratic pair on a
Clifford algebra and triality*, which computes the three trialitarian slots of
an orthogonal sum built from four quaternion algebras whose tensor product is
split.

The final equivalence isolates the simultaneous quaternion-factor theorem
that remains genuinely geometric.  It is not supplied by the exponent-two
abelian-group calculation formalized here.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u

/-- An additive commutative group has exponent two when every element is its
own additive inverse.  This is the formal abstraction of `Br(k)[2]`. -/
def IsExponentTwo (A : Type u) [AddCommGroup A] : Prop :=
  ∀ x : A, x + x = 0

/-- The three Brauer classes in the E7 triality target. -/
structure BrauerPacket (A : Type u) where
  underlying : A
  cliffordPlus : A
  cliffordMinus : A

namespace BrauerPacket

variable {A : Type u}

/-- Extensionality for the three labelled Brauer classes. -/
@[ext] theorem ext {P Q : BrauerPacket A}
    (hUnderlying : P.underlying = Q.underlying)
    (hPlus : P.cliffordPlus = Q.cliffordPlus)
    (hMinus : P.cliffordMinus = Q.cliffordMinus) : P = Q := by
  cases P
  cases Q
  cases hUnderlying
  cases hPlus
  cases hMinus
  rfl

variable [AddCommGroup A]

/-- The packet attached to three quaternion Brauer classes. -/
def ofTriple (q₁ q₂ q₃ : A) : BrauerPacket A where
  underlying := q₂ + q₃
  cliffordPlus := q₁ + q₂
  cliffordMinus := q₁ + q₃

@[simp] theorem ofTriple_underlying (q₁ q₂ q₃ : A) :
    (ofTriple q₁ q₂ q₃).underlying = q₂ + q₃ := rfl

@[simp] theorem ofTriple_cliffordPlus (q₁ q₂ q₃ : A) :
    (ofTriple q₁ q₂ q₃).cliffordPlus = q₁ + q₂ := rfl

@[simp] theorem ofTriple_cliffordMinus (q₁ q₂ q₃ : A) :
    (ofTriple q₁ q₂ q₃).cliffordMinus = q₁ + q₃ := rfl

/-- Adding one class to all three inputs leaves every pairwise sum unchanged. -/
theorem ofTriple_add_diagonal
    (h₂ : IsExponentTwo A) (q₁ q₂ q₃ r : A) :
    ofTriple (q₁ + r) (q₂ + r) (q₃ + r) = ofTriple q₁ q₂ q₃ := by
  apply BrauerPacket.ext
  · change (q₂ + r) + (q₃ + r) = q₂ + q₃
    calc
      (q₂ + r) + (q₃ + r) = (q₂ + q₃) + (r + r) := by abel
      _ = q₂ + q₃ := by rw [h₂ r, add_zero]
  · change (q₁ + r) + (q₂ + r) = q₁ + q₂
    calc
      (q₁ + r) + (q₂ + r) = (q₁ + q₂) + (r + r) := by abel
      _ = q₁ + q₂ := by rw [h₂ r, add_zero]
  · change (q₁ + r) + (q₃ + r) = q₁ + q₃
    calc
      (q₁ + r) + (q₃ + r) = (q₁ + q₃) + (r + r) := by abel
      _ = q₁ + q₃ := by rw [h₂ r, add_zero]

/-- The three entries of a pairwise Brauer packet sum to zero. -/
theorem ofTriple_balanced
    (h₂ : IsExponentTwo A) (q₁ q₂ q₃ : A) :
    (ofTriple q₁ q₂ q₃).underlying +
        (ofTriple q₁ q₂ q₃).cliffordPlus +
        (ofTriple q₁ q₂ q₃).cliffordMinus = 0 := by
  change (q₂ + q₃) + (q₁ + q₂) + (q₁ + q₃) = 0
  calc
    (q₂ + q₃) + (q₁ + q₂) + (q₁ + q₃) =
        (q₁ + q₁) + (q₂ + q₂) + (q₃ + q₃) := by abel
    _ = 0 := by rw [h₂ q₁, h₂ q₂, h₂ q₃]; simp

/-- Equality of packets is exactly equality of triples modulo diagonal
translation.  This is the intrinsic form of the rank-two incidence
calculation over `F₂`. -/
theorem ofTriple_eq_iff_diagonal
    (h₂ : IsExponentTwo A)
    (q₁ q₂ q₃ q₁' q₂' q₃' : A) :
    ofTriple q₁ q₂ q₃ = ofTriple q₁' q₂' q₃' ↔
      ∃ r : A,
        q₁' = q₁ + r ∧ q₂' = q₂ + r ∧ q₃' = q₃ + r := by
  constructor
  · intro h
    have h₁₂ := congrArg BrauerPacket.cliffordPlus h
    have h₁₃ := congrArg BrauerPacket.cliffordMinus h
    change q₁ + q₂ = q₁' + q₂' at h₁₂
    change q₁ + q₃ = q₁' + q₃' at h₁₃
    let r : A := q₁' + q₁
    refine ⟨r, ?_, ?_, ?_⟩
    · symm
      change q₁ + (q₁' + q₁) = q₁'
      calc
        q₁ + (q₁' + q₁) = q₁' + (q₁ + q₁) := by abel
        _ = q₁' := by rw [h₂ q₁, add_zero]
    · change q₂' = q₂ + (q₁' + q₁)
      calc
        q₂' = (q₁' + q₂') + q₁' := by
          calc
            q₂' = q₂' + 0 := by simp
            _ = q₂' + (q₁' + q₁') := by rw [h₂ q₁']
            _ = (q₁' + q₂') + q₁' := by abel
        _ = (q₁ + q₂) + q₁' := by rw [← h₁₂]
        _ = q₂ + (q₁' + q₁) := by abel
    · change q₃' = q₃ + (q₁' + q₁)
      calc
        q₃' = (q₁' + q₃') + q₁' := by
          calc
            q₃' = q₃' + 0 := by simp
            _ = q₃' + (q₁' + q₁') := by rw [h₂ q₁']
            _ = (q₁' + q₃') + q₁' := by abel
        _ = (q₁ + q₃) + q₁' := by rw [← h₁₃]
        _ = q₃ + (q₁' + q₁) := by abel
  · rintro ⟨r, rfl, rfl, rfl⟩
    exact (ofTriple_add_diagonal h₂ q₁ q₂ q₃ r).symm

/-- Conversely, every balanced three-class packet is represented by a triple.
The representing triple is unique only modulo diagonal translation. -/
theorem exists_of_balanced
    (h₂ : IsExponentTwo A) (P : BrauerPacket A)
    (hP : P.underlying + P.cliffordPlus + P.cliffordMinus = 0) :
    ∃ q₁ q₂ q₃ : A, ofTriple q₁ q₂ q₃ = P := by
  have hu : P.cliffordPlus + P.cliffordMinus = P.underlying := by
    calc
      P.cliffordPlus + P.cliffordMinus =
          (P.underlying + P.underlying) +
            (P.cliffordPlus + P.cliffordMinus) := by
              rw [h₂ P.underlying, zero_add]
      _ = (P.underlying + P.cliffordPlus + P.cliffordMinus) +
            P.underlying := by abel
      _ = P.underlying := by rw [hP, zero_add]
  refine ⟨0, P.cliffordPlus, P.cliffordMinus, ?_⟩
  apply BrauerPacket.ext
  · simpa [ofTriple] using hu
  · simp [ofTriple]
  · simp [ofTriple]

end BrauerPacket

variable {A : Type u} [AddCommGroup A]

/-- Four Brauer classes used in the orthogonal-sum construction. -/
structure FourClassPacket (A : Type u) where
  p₁ : A
  p₂ : A
  p₃ : A
  p₄ : A

namespace FourClassPacket

/-- The sum of the four classes.  Vanishing means that their tensor product is
split at the Brauer-class level. -/
def total (P : FourClassPacket A) : A := P.p₁ + P.p₂ + P.p₃ + P.p₄

/-- The three primary pairings appearing in the orthogonal-sum triality
formula. -/
def brauerPacket (P : FourClassPacket A) : BrauerPacket A where
  underlying := P.p₁ + P.p₂
  cliffordPlus := P.p₁ + P.p₃
  cliffordMinus := P.p₁ + P.p₄

/-- The canonical four-class packet determined by an auxiliary class `r`. -/
def completion (q₁ q₂ q₃ r : A) : FourClassPacket A where
  p₁ := r
  p₂ := r + q₂ + q₃
  p₃ := r + q₁ + q₂
  p₄ := r + q₁ + q₃

/-- Every canonical completion has split total Brauer class. -/
theorem completion_total
    (h₂ : IsExponentTwo A) (q₁ q₂ q₃ r : A) :
    (completion q₁ q₂ q₃ r).total = 0 := by
  change r + (r + q₂ + q₃) + (r + q₁ + q₂) + (r + q₁ + q₃) = 0
  calc
    r + (r + q₂ + q₃) + (r + q₁ + q₂) + (r + q₁ + q₃) =
        (r + r) + (r + r) + (q₁ + q₁) + (q₂ + q₂) + (q₃ + q₃) := by
          abel
    _ = 0 := by rw [h₂ r, h₂ q₁, h₂ q₂, h₂ q₃]; simp

/-- The three primary pairings of the canonical completion are exactly the
E7 target packet. -/
theorem completion_brauerPacket
    (h₂ : IsExponentTwo A) (q₁ q₂ q₃ r : A) :
    (completion q₁ q₂ q₃ r).brauerPacket =
      BrauerPacket.ofTriple q₁ q₂ q₃ := by
  apply BrauerPacket.ext
  · change r + (r + q₂ + q₃) = q₂ + q₃
    calc
      r + (r + q₂ + q₃) = (r + r) + (q₂ + q₃) := by abel
      _ = q₂ + q₃ := by rw [h₂ r, zero_add]
  · change r + (r + q₁ + q₂) = q₁ + q₂
    calc
      r + (r + q₁ + q₂) = (r + r) + (q₁ + q₂) := by abel
      _ = q₁ + q₂ := by rw [h₂ r, zero_add]
  · change r + (r + q₁ + q₃) = q₁ + q₃
    calc
      r + (r + q₁ + q₃) = (r + r) + (q₁ + q₃) := by abel
      _ = q₁ + q₃ := by rw [h₂ r, zero_add]

/-- The complementary pairings agree with the same target packet. -/
theorem completion_complementary_pairings
    (h₂ : IsExponentTwo A) (q₁ q₂ q₃ r : A) :
    let P := completion q₁ q₂ q₃ r
    P.p₃ + P.p₄ = q₂ + q₃ ∧
      P.p₂ + P.p₄ = q₁ + q₂ ∧
      P.p₂ + P.p₃ = q₁ + q₃ := by
  dsimp [completion]
  constructor
  · calc
      (r + q₁ + q₂) + (r + q₁ + q₃) =
          (r + r) + (q₁ + q₁) + (q₂ + q₃) := by abel
      _ = q₂ + q₃ := by rw [h₂ r, h₂ q₁]; simp
  constructor
  · calc
      (r + q₂ + q₃) + (r + q₁ + q₃) =
          (r + r) + (q₃ + q₃) + (q₁ + q₂) := by abel
      _ = q₁ + q₂ := by rw [h₂ r, h₂ q₃]; simp
  · calc
      (r + q₂ + q₃) + (r + q₁ + q₂) =
          (r + r) + (q₂ + q₂) + (q₁ + q₃) := by abel
      _ = q₁ + q₃ := by rw [h₂ r, h₂ q₂]; simp

end FourClassPacket

/-- A class predicate has a quaternion completion for `(q₁,q₂,q₃)` when one
can choose the four entries of the canonical packet inside that predicate. -/
def HasQuaternionCompletion
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) : Prop :=
  ∃ r : A,
    IsQuaternionClass r ∧
      IsQuaternionClass (r + q₂ + q₃) ∧
      IsQuaternionClass (r + q₁ + q₂) ∧
      IsQuaternionClass (r + q₁ + q₃)

/-- The exact four-quaternion presentation needed by the published
orthogonal-sum construction. -/
def HasFourQuaternionPresentation
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) : Prop :=
  ∃ P : FourClassPacket A,
    (IsQuaternionClass P.p₁ ∧ IsQuaternionClass P.p₂ ∧
      IsQuaternionClass P.p₃ ∧ IsQuaternionClass P.p₄) ∧
    P.total = 0 ∧
    P.brauerPacket = BrauerPacket.ofTriple q₁ q₂ q₃

/-- Quaternion completion and a four-quaternion orthogonal-sum packet are
exactly equivalent at the Brauer-class level. -/
theorem hasFourQuaternionPresentation_iff_completion
    (h₂ : IsExponentTwo A)
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) :
    HasFourQuaternionPresentation IsQuaternionClass q₁ q₂ q₃ ↔
      HasQuaternionCompletion IsQuaternionClass q₁ q₂ q₃ := by
  constructor
  · rintro ⟨P, hQ, _htotal, hpacket⟩
    have hunderlying := congrArg BrauerPacket.underlying hpacket
    have hplus := congrArg BrauerPacket.cliffordPlus hpacket
    have hminus := congrArg BrauerPacket.cliffordMinus hpacket
    change P.p₁ + P.p₂ = q₂ + q₃ at hunderlying
    change P.p₁ + P.p₃ = q₁ + q₂ at hplus
    change P.p₁ + P.p₄ = q₁ + q₃ at hminus
    have hp₂ : P.p₁ + q₂ + q₃ = P.p₂ := by
      calc
        P.p₁ + q₂ + q₃ = P.p₁ + (q₂ + q₃) := by abel
        _ = P.p₁ + (P.p₁ + P.p₂) := by rw [← hunderlying]
        _ = (P.p₁ + P.p₁) + P.p₂ := by abel
        _ = P.p₂ := by rw [h₂ P.p₁, zero_add]
    have hp₃ : P.p₁ + q₁ + q₂ = P.p₃ := by
      calc
        P.p₁ + q₁ + q₂ = P.p₁ + (q₁ + q₂) := by abel
        _ = P.p₁ + (P.p₁ + P.p₃) := by rw [← hplus]
        _ = (P.p₁ + P.p₁) + P.p₃ := by abel
        _ = P.p₃ := by rw [h₂ P.p₁, zero_add]
    have hp₄ : P.p₁ + q₁ + q₃ = P.p₄ := by
      calc
        P.p₁ + q₁ + q₃ = P.p₁ + (q₁ + q₃) := by abel
        _ = P.p₁ + (P.p₁ + P.p₄) := by rw [← hminus]
        _ = (P.p₁ + P.p₁) + P.p₄ := by abel
        _ = P.p₄ := by rw [h₂ P.p₁, zero_add]
    refine ⟨P.p₁, hQ.1, ?_, ?_, ?_⟩
    · rw [hp₂]
      exact hQ.2.1
    · rw [hp₃]
      exact hQ.2.2.1
    · rw [hp₄]
      exact hQ.2.2.2
  · rintro ⟨r, hr, hp₂, hp₃, hp₄⟩
    let P := FourClassPacket.completion q₁ q₂ q₃ r
    refine ⟨P, ?_, ?_, ?_⟩
    · exact ⟨hr, hp₂, hp₃, hp₄⟩
    · exact FourClassPacket.completion_total h₂ q₁ q₂ q₃ r
    · exact FourClassPacket.completion_brauerPacket h₂ q₁ q₂ q₃ r

/-- A concrete sufficient case: if the total class `q₁+q₂+q₃` is itself a
quaternion class, it supplies the auxiliary class and the other three entries
reduce to `q₁`, `q₃`, and `q₂`. -/
theorem hasQuaternionCompletion_of_total
    (h₂ : IsExponentTwo A)
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A)
    (hq₁ : IsQuaternionClass q₁)
    (hq₂ : IsQuaternionClass q₂)
    (hq₃ : IsQuaternionClass q₃)
    (htotal : IsQuaternionClass (q₁ + q₂ + q₃)) :
    HasQuaternionCompletion IsQuaternionClass q₁ q₂ q₃ := by
  refine ⟨q₁ + q₂ + q₃, htotal, ?_, ?_, ?_⟩
  · have h : (q₁ + q₂ + q₃) + q₂ + q₃ = q₁ := by
      calc
        (q₁ + q₂ + q₃) + q₂ + q₃ =
            q₁ + (q₂ + q₂) + (q₃ + q₃) := by abel
        _ = q₁ := by rw [h₂ q₂, h₂ q₃]; simp
    rw [h]
    exact hq₁
  · have h : (q₁ + q₂ + q₃) + q₁ + q₂ = q₃ := by
      calc
        (q₁ + q₂ + q₃) + q₁ + q₂ =
            (q₁ + q₁) + (q₂ + q₂) + q₃ := by abel
        _ = q₃ := by rw [h₂ q₁, h₂ q₂]; simp
    rw [h]
    exact hq₃
  · have h : (q₁ + q₂ + q₃) + q₁ + q₃ = q₂ := by
      calc
        (q₁ + q₂ + q₃) + q₁ + q₃ =
            (q₁ + q₁) + q₂ + (q₃ + q₃) := by abel
        _ = q₂ := by rw [h₂ q₁, h₂ q₃]; simp
    rw [h]
    exact hq₂

/-- Three biquaternion classes have a simultaneous quaternion factor when each
can be written as the sum of one common quaternion class and one residual
quaternion class.  This is the exact symbol-geometry content left by the
four-quaternion orthogonal-sum construction. -/
def HasSimultaneousQuaternionFactor
    (IsQuaternionClass : A → Prop) (h₂₃ h₁₂ h₁₃ : A) : Prop :=
  ∃ r p₂₃ p₁₂ p₁₃ : A,
    IsQuaternionClass r ∧
      IsQuaternionClass p₂₃ ∧
      IsQuaternionClass p₁₂ ∧
      IsQuaternionClass p₁₃ ∧
      h₂₃ = r + p₂₃ ∧
      h₁₂ = r + p₁₂ ∧
      h₁₃ = r + p₁₃

/-- Quaternion completion is equivalent to finding one simultaneous quaternion
factor for the three pairwise-sum biquaternion classes. -/
theorem hasQuaternionCompletion_iff_simultaneousQuaternionFactor
    (h₂ : IsExponentTwo A)
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) :
    HasQuaternionCompletion IsQuaternionClass q₁ q₂ q₃ ↔
      HasSimultaneousQuaternionFactor IsQuaternionClass
        (q₂ + q₃) (q₁ + q₂) (q₁ + q₃) := by
  constructor
  · rintro ⟨r, hr, hp₂₃, hp₁₂, hp₁₃⟩
    refine ⟨r, r + q₂ + q₃, r + q₁ + q₂, r + q₁ + q₃,
      hr, hp₂₃, hp₁₂, hp₁₃, ?_, ?_, ?_⟩
    · calc
        q₂ + q₃ = (r + r) + (q₂ + q₃) := by rw [h₂ r, zero_add]
        _ = r + (r + q₂ + q₃) := by abel
    · calc
        q₁ + q₂ = (r + r) + (q₁ + q₂) := by rw [h₂ r, zero_add]
        _ = r + (r + q₁ + q₂) := by abel
    · calc
        q₁ + q₃ = (r + r) + (q₁ + q₃) := by rw [h₂ r, zero_add]
        _ = r + (r + q₁ + q₃) := by abel
  · rintro ⟨r, p₂₃, p₁₂, p₁₃, hr, hp₂₃, hp₁₂, hp₁₃,
      h₂₃, h₁₂, h₁₃⟩
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · have h : r + q₂ + q₃ = p₂₃ := by
        calc
          r + q₂ + q₃ = r + (q₂ + q₃) := by abel
          _ = r + (r + p₂₃) := by rw [h₂₃]
          _ = (r + r) + p₂₃ := by abel
          _ = p₂₃ := by rw [h₂ r, zero_add]
      rw [h]
      exact hp₂₃
    · have h : r + q₁ + q₂ = p₁₂ := by
        calc
          r + q₁ + q₂ = r + (q₁ + q₂) := by abel
          _ = r + (r + p₁₂) := by rw [h₁₂]
          _ = (r + r) + p₁₂ := by abel
          _ = p₁₂ := by rw [h₂ r, zero_add]
      rw [h]
      exact hp₁₂
    · have h : r + q₁ + q₃ = p₁₃ := by
        calc
          r + q₁ + q₃ = r + (q₁ + q₃) := by abel
          _ = r + (r + p₁₃) := by rw [h₁₃]
          _ = (r + r) + p₁₃ := by abel
          _ = p₁₃ := by rw [h₂ r, zero_add]
      rw [h]
      exact hp₁₃

/-- A second concrete sufficient case: if the three pairwise sums are already
quaternion classes, the split class is a simultaneous factor. -/
theorem hasQuaternionCompletion_of_pairwise
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A)
    (hzero : IsQuaternionClass 0)
    (h₂₃ : IsQuaternionClass (q₂ + q₃))
    (h₁₂ : IsQuaternionClass (q₁ + q₂))
    (h₁₃ : IsQuaternionClass (q₁ + q₃)) :
    HasQuaternionCompletion IsQuaternionClass q₁ q₂ q₃ := by
  refine ⟨0, hzero, ?_, ?_, ?_⟩
  · simpa using h₂₃
  · simpa using h₁₂
  · simpa using h₁₃

end RiemannResearch.E7.QuaternionTrialityPacket
