import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Abel

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u

def IsExponentTwo (A : Type u) [AddCommGroup A] : Prop :=
  ∀ x : A, x + x = 0

structure BrauerPacket (A : Type u) where
  underlying : A
  cliffordPlus : A
  cliffordMinus : A

namespace BrauerPacket

variable {A : Type u}

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

def ofTriple (q₁ q₂ q₃ : A) : BrauerPacket A where
  underlying := q₂ + q₃
  cliffordPlus := q₁ + q₂
  cliffordMinus := q₁ + q₃

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

end BrauerPacket

variable {A : Type u} [AddCommGroup A]

structure FourClassPacket (A : Type u) where
  p₁ : A
  p₂ : A
  p₃ : A
  p₄ : A

namespace FourClassPacket

def total (P : FourClassPacket A) : A := P.p₁ + P.p₂ + P.p₃ + P.p₄

def brauerPacket (P : FourClassPacket A) : BrauerPacket A where
  underlying := P.p₁ + P.p₂
  cliffordPlus := P.p₁ + P.p₃
  cliffordMinus := P.p₁ + P.p₄

def completion (q₁ q₂ q₃ r : A) : FourClassPacket A where
  p₁ := r
  p₂ := r + q₂ + q₃
  p₃ := r + q₁ + q₂
  p₄ := r + q₁ + q₃

theorem completion_total
    (h₂ : IsExponentTwo A) (q₁ q₂ q₃ r : A) :
    (completion q₁ q₂ q₃ r).total = 0 := by
  change r + (r + q₂ + q₃) + (r + q₁ + q₂) + (r + q₁ + q₃) = 0
  calc
    r + (r + q₂ + q₃) + (r + q₁ + q₂) + (r + q₁ + q₃) =
        (r + r) + (r + r) + (q₁ + q₁) + (q₂ + q₂) + (q₃ + q₃) := by abel
    _ = 0 := by rw [h₂ r, h₂ q₁, h₂ q₂, h₂ q₃]; simp

theorem completion_brauerPacket
    (h₂ : IsExponentTwo A) (q₁ q₂ q₃ r : A) :
    (completion q₁ q₂ q₃ r).brauerPacket = BrauerPacket.ofTriple q₁ q₂ q₃ := by
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

end FourClassPacket

def HasQuaternionCompletion
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) : Prop :=
  ∃ r : A,
    IsQuaternionClass r ∧
      IsQuaternionClass (r + q₂ + q₃) ∧
      IsQuaternionClass (r + q₁ + q₂) ∧
      IsQuaternionClass (r + q₁ + q₃)

def HasFourQuaternionPresentation
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) : Prop :=
  ∃ P : FourClassPacket A,
    (IsQuaternionClass P.p₁ ∧ IsQuaternionClass P.p₂ ∧
      IsQuaternionClass P.p₃ ∧ IsQuaternionClass P.p₄) ∧
    P.total = 0 ∧
    P.brauerPacket = BrauerPacket.ofTriple q₁ q₂ q₃

theorem hasFourQuaternionPresentation_iff_completion
    (h₂ : IsExponentTwo A)
    (IsQuaternionClass : A → Prop) (q₁ q₂ q₃ : A) :
    HasFourQuaternionPresentation IsQuaternionClass q₁ q₂ q₃ ↔
      HasQuaternionCompletion IsQuaternionClass q₁ q₂ q₃ := by
  constructor
  · rintro ⟨P, hQ, _hTotal, hPacket⟩
    have hu := congrArg BrauerPacket.underlying hPacket
    have hp := congrArg BrauerPacket.cliffordPlus hPacket
    have hm := congrArg BrauerPacket.cliffordMinus hPacket
    change P.p₁ + P.p₂ = q₂ + q₃ at hu
    change P.p₁ + P.p₃ = q₁ + q₂ at hp
    change P.p₁ + P.p₄ = q₁ + q₃ at hm
    refine ⟨P.p₁, hQ.1, ?_, ?_, ?_⟩
    · convert hQ.2.1 using 1
      calc
        P.p₁ + q₂ + q₃ = P.p₁ + (q₂ + q₃) := by abel
        _ = P.p₁ + (P.p₁ + P.p₂) := by rw [← hu]
        _ = P.p₂ := by rw [← add_assoc, h₂ P.p₁, zero_add]
    · convert hQ.2.2.1 using 1
      calc
        P.p₁ + q₁ + q₂ = P.p₁ + (q₁ + q₂) := by abel
        _ = P.p₁ + (P.p₁ + P.p₃) := by rw [← hp]
        _ = P.p₃ := by rw [← add_assoc, h₂ P.p₁, zero_add]
    · convert hQ.2.2.2 using 1
      calc
        P.p₁ + q₁ + q₃ = P.p₁ + (q₁ + q₃) := by abel
        _ = P.p₁ + (P.p₁ + P.p₄) := by rw [← hm]
        _ = P.p₄ := by rw [← add_assoc, h₂ P.p₁, zero_add]
  · rintro ⟨r, hr, hp₂, hp₃, hp₄⟩
    refine ⟨FourClassPacket.completion q₁ q₂ q₃ r,
      ⟨hr, hp₂, hp₃, hp₄⟩,
      FourClassPacket.completion_total h₂ q₁ q₂ q₃ r,
      FourClassPacket.completion_brauerPacket h₂ q₁ q₂ q₃ r⟩

end RiemannResearch.E7.QuaternionTrialityPacket
