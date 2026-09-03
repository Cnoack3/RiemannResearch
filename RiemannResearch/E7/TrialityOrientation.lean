/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionTrialityPacket

/-!
# The labelled triality action on the E7 Brauer packet

The remaining type-`E7` bridge is not an unoriented Brauer-class statement.
The three entries of the associated inner `D4` packet are labelled by the
vector and two half-spin representations.  This file records the two standard
generators of the diagram-triality action directly on `BrauerPacket`:

* `rotate` cyclically permutes the three labels;
* `reflect` exchanges the two half-spin labels.

Their relations are the presentation of `S₃`, and the action agrees with the
corresponding permutations of the three quaternion inputs.  These are purely
formal identities; no existence of a degree-eight quadratic pair is assumed.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u

variable {A : Type u} [AddCommGroup A]

namespace BrauerPacket

/-- Cyclic triality relabelling: vector, positive half-spin, negative half-spin. -/
def rotate (P : BrauerPacket A) : BrauerPacket A where
  underlying := P.cliffordPlus
  cliffordPlus := P.cliffordMinus
  cliffordMinus := P.underlying

/-- The order-two diagram symmetry fixing the vector label and exchanging the
half-spin labels. -/
def reflect (P : BrauerPacket A) : BrauerPacket A where
  underlying := P.underlying
  cliffordPlus := P.cliffordMinus
  cliffordMinus := P.cliffordPlus

@[simp] theorem rotate_underlying (P : BrauerPacket A) :
    (rotate P).underlying = P.cliffordPlus := rfl

@[simp] theorem rotate_cliffordPlus (P : BrauerPacket A) :
    (rotate P).cliffordPlus = P.cliffordMinus := rfl

@[simp] theorem rotate_cliffordMinus (P : BrauerPacket A) :
    (rotate P).cliffordMinus = P.underlying := rfl

@[simp] theorem reflect_underlying (P : BrauerPacket A) :
    (reflect P).underlying = P.underlying := rfl

@[simp] theorem reflect_cliffordPlus (P : BrauerPacket A) :
    (reflect P).cliffordPlus = P.cliffordMinus := rfl

@[simp] theorem reflect_cliffordMinus (P : BrauerPacket A) :
    (reflect P).cliffordMinus = P.cliffordPlus := rfl

/-- The cyclic triality relabelling has order three. -/
@[simp] theorem rotate_three (P : BrauerPacket A) :
    rotate (rotate (rotate P)) = P := by
  cases P
  rfl

/-- The half-spin reflection has order two. -/
@[simp] theorem reflect_two (P : BrauerPacket A) :
    reflect (reflect P) = P := by
  cases P
  rfl

/-- The standard `S₃` relation `srs = r²`. -/
theorem reflect_rotate_reflect (P : BrauerPacket A) :
    reflect (rotate (reflect P)) = rotate (rotate P) := by
  cases P
  rfl

/-- Cyclic relabelling agrees with the cyclic permutation of quaternion inputs. -/
theorem rotate_ofTriple (q₁ q₂ q₃ : A) :
    rotate (ofTriple q₁ q₂ q₃) = ofTriple q₃ q₁ q₂ := by
  apply BrauerPacket.ext
  · simp [rotate, ofTriple]
  · simp [rotate, ofTriple, add_comm]
  · simp [rotate, ofTriple, add_comm]

/-- The half-spin reflection agrees with interchanging the second and third
quaternion inputs. -/
theorem reflect_ofTriple (q₁ q₂ q₃ : A) :
    reflect (ofTriple q₁ q₂ q₃) = ofTriple q₁ q₃ q₂ := by
  apply BrauerPacket.ext
  · simp [reflect, ofTriple, add_comm]
  · simp [reflect, ofTriple]
  · simp [reflect, ofTriple]

/-- A labelled packet satisfies the unique linear relation among the three
nontrivial central characters of `Spin₈`. -/
def IsBalanced (P : BrauerPacket A) : Prop :=
  P.underlying + P.cliffordPlus + P.cliffordMinus = 0

/-- Cyclic triality preserves the central-character relation. -/
theorem isBalanced_rotate {P : BrauerPacket A} (hP : IsBalanced P) :
    IsBalanced (rotate P) := by
  change P.cliffordPlus + P.cliffordMinus + P.underlying = 0
  calc
    P.cliffordPlus + P.cliffordMinus + P.underlying =
        P.underlying + P.cliffordPlus + P.cliffordMinus := by abel
    _ = 0 := hP

/-- The half-spin reflection preserves the central-character relation. -/
theorem isBalanced_reflect {P : BrauerPacket A} (hP : IsBalanced P) :
    IsBalanced (reflect P) := by
  change P.underlying + P.cliffordMinus + P.cliffordPlus = 0
  calc
    P.underlying + P.cliffordMinus + P.cliffordPlus =
        P.underlying + P.cliffordPlus + P.cliffordMinus := by abel
    _ = 0 := hP

/-- Every packet arising from three exponent-two classes is balanced. -/
theorem isBalanced_ofTriple
    (h₂ : IsExponentTwo A) (q₁ q₂ q₃ : A) :
    IsBalanced (ofTriple q₁ q₂ q₃) :=
  ofTriple_balanced h₂ q₁ q₂ q₃

/-- Balanced packets are exactly the packets arising from three exponent-two
classes. Thus balance is the entire additive content of a triality packet. -/
theorem isBalanced_iff_exists_ofTriple
    (h₂ : IsExponentTwo A) (P : BrauerPacket A) :
    IsBalanced P ↔ ∃ q₁ q₂ q₃ : A, ofTriple q₁ q₂ q₃ = P := by
  constructor
  · intro hP
    exact exists_of_balanced h₂ P hP
  · rintro ⟨q₁, q₂, q₃, rfl⟩
    exact isBalanced_ofTriple h₂ q₁ q₂ q₃

/-- To prove an additive property of every triple packet is equivalent to
proving it for every balanced packet. -/
theorem forall_ofTriple_iff_forall_balanced
    (h₂ : IsExponentTwo A) (Special : BrauerPacket A → Prop) :
    (∀ q₁ q₂ q₃ : A, Special (ofTriple q₁ q₂ q₃)) ↔
      ∀ P : BrauerPacket A, IsBalanced P → Special P := by
  constructor
  · intro h P hP
    rcases exists_of_balanced h₂ P hP with ⟨q₁, q₂, q₃, rfl⟩
    exact h q₁ q₂ q₃
  · intro h q₁ q₂ q₃
    exact h (ofTriple q₁ q₂ q₃)
      (isBalanced_ofTriple h₂ q₁ q₂ q₃)

end BrauerPacket

end RiemannResearch.E7.QuaternionTrialityPacket
