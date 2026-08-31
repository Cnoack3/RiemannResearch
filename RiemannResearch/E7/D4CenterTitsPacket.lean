/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.TrialityOrientation
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The centre of Spin(8) and balanced labelled Tits packets

For split simply connected type `D₄`, the character group of the centre is a
two-dimensional `𝔽₂`-vector space.  Its three nonzero characters label the
vector and the two half-spin representations.  A degree-two cohomology class
with values in that centre therefore produces three Brauer classes whose sum
is zero.

This file formalizes that root-datum layer.  For every `ZMod 2`-module `A`,
linear maps from the central character group to `A` are equivalent to balanced
labelled `BrauerPacket A`s.  In the intended application, `A` is the
2-primary Brauer group and the still-missing theorem is not this linear
classification: it is effectivity of the corresponding nonabelian
`PGO₈⁺` boundary class by an actual quadratic pair.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u

/-- The character group of `Z(Spin₈) ≃ μ₂ × μ₂`. -/
abbrev D4CenterCharacter := Fin 2 → ZMod 2

/-- The character of the vector representation. -/
def vectorCharacter : D4CenterCharacter :=
  fun i => if i = 0 then 1 else 0

/-- The character of the positive half-spin representation. -/
def spinPlusCharacter : D4CenterCharacter :=
  fun i => if i = 1 then 1 else 0

/-- The character of the negative half-spin representation. -/
def spinMinusCharacter : D4CenterCharacter :=
  vectorCharacter + spinPlusCharacter

/-- The three representation characters are precisely the three nonzero
characters of the centre. -/
theorem d4CenterCharacter_classification :
    ∀ χ : D4CenterCharacter,
      χ = 0 ∨ χ = vectorCharacter ∨
        χ = spinPlusCharacter ∨ χ = spinMinusCharacter := by
  decide

@[simp] theorem vectorCharacter_ne_zero : vectorCharacter ≠ 0 := by
  decide

@[simp] theorem spinPlusCharacter_ne_zero : spinPlusCharacter ≠ 0 := by
  decide

@[simp] theorem spinMinusCharacter_ne_zero : spinMinusCharacter ≠ 0 := by
  decide

/-- The unique relation among the three nonzero central characters. -/
theorem d4Character_sum :
    vectorCharacter + spinPlusCharacter + spinMinusCharacter = 0 := by
  decide

/-- Every central character is the indicated linear combination of the vector
and positive half-spin characters. -/
theorem d4Character_decomposition (χ : D4CenterCharacter) :
    χ = χ 0 • vectorCharacter + χ 1 • spinPlusCharacter := by
  ext i
  fin_cases i <;> simp [vectorCharacter, spinPlusCharacter, smul_eq_mul]

variable {A : Type u} [AddCommGroup A] [Module (ZMod 2) A]

/-- A `ZMod 2`-module is automatically an exponent-two additive group. -/
theorem module_isExponentTwo : IsExponentTwo A := by
  intro x
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  calc
    x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by simp
    _ = ((1 : ZMod 2) + 1) • x := by rw [add_smul]
    _ = 0 := by rw [h, zero_smul]

/-- The linear central Tits datum determined by its vector and positive
half-spin values. -/
def centralTitsMap (underlying cliffordPlus : A) :
    D4CenterCharacter →ₗ[ZMod 2] A where
  toFun := fun χ => χ 0 • underlying + χ 1 • cliffordPlus
  map_add' := by
    intro χ ψ
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' := by
    intro c χ
    simp [Pi.smul_apply, smul_add, smul_eq_mul, mul_smul]

@[simp] theorem centralTitsMap_vectorCharacter
    (underlying cliffordPlus : A) :
    centralTitsMap underlying cliffordPlus vectorCharacter = underlying := by
  simp [centralTitsMap, vectorCharacter]

@[simp] theorem centralTitsMap_spinPlusCharacter
    (underlying cliffordPlus : A) :
    centralTitsMap underlying cliffordPlus spinPlusCharacter = cliffordPlus := by
  simp [centralTitsMap, spinPlusCharacter]

@[simp] theorem centralTitsMap_spinMinusCharacter
    (underlying cliffordPlus : A) :
    centralTitsMap underlying cliffordPlus spinMinusCharacter =
      underlying + cliffordPlus := by
  simp [centralTitsMap, spinMinusCharacter, vectorCharacter,
    spinPlusCharacter]

/-- Evaluate a central Tits datum on the three labelled nonzero characters. -/
def packetOfCentralTitsMap
    (t : D4CenterCharacter →ₗ[ZMod 2] A) : BrauerPacket A where
  underlying := t vectorCharacter
  cliffordPlus := t spinPlusCharacter
  cliffordMinus := t spinMinusCharacter

/-- Every central Tits datum gives a balanced labelled packet. -/
theorem packetOfCentralTitsMap_isBalanced
    (t : D4CenterCharacter →ₗ[ZMod 2] A) :
    BrauerPacket.IsBalanced (packetOfCentralTitsMap t) := by
  change t vectorCharacter + t spinPlusCharacter + t spinMinusCharacter = 0
  rw [← t.map_add, ← t.map_add, d4Character_sum, t.map_zero]

/-- A linear central Tits datum is determined by the vector and positive
half-spin entries of its packet. -/
theorem centralTitsMap_of_values
    (t : D4CenterCharacter →ₗ[ZMod 2] A) :
    centralTitsMap (t vectorCharacter) (t spinPlusCharacter) = t := by
  apply LinearMap.ext
  intro χ
  change χ 0 • t vectorCharacter + χ 1 • t spinPlusCharacter = t χ
  calc
    χ 0 • t vectorCharacter + χ 1 • t spinPlusCharacter =
        t (χ 0 • vectorCharacter + χ 1 • spinPlusCharacter) := by simp
    _ = t χ := by rw [← d4Character_decomposition χ]

/-- Evaluation on the three nonzero central characters is injective. -/
theorem packetOfCentralTitsMap_injective :
    Function.Injective
      (packetOfCentralTitsMap :
        (D4CenterCharacter →ₗ[ZMod 2] A) → BrauerPacket A) := by
  intro t s h
  have hv := congrArg BrauerPacket.underlying h
  have hs := congrArg BrauerPacket.cliffordPlus h
  change t vectorCharacter = s vectorCharacter at hv
  change t spinPlusCharacter = s spinPlusCharacter at hs
  calc
    t = centralTitsMap (t vectorCharacter) (t spinPlusCharacter) :=
      (centralTitsMap_of_values t).symm
    _ = centralTitsMap (s vectorCharacter) (s spinPlusCharacter) := by
      rw [hv, hs]
    _ = s := centralTitsMap_of_values s

/-- Reconstructing from the first two labelled values recovers every balanced
packet. -/
theorem packetOfCentralTitsMap_centralTitsMap_of_isBalanced
    (P : BrauerPacket A) (hP : BrauerPacket.IsBalanced P) :
    packetOfCentralTitsMap
        (centralTitsMap P.underlying P.cliffordPlus) = P := by
  have hMinus : P.cliffordMinus = P.underlying + P.cliffordPlus := by
    have h₂ : IsExponentTwo A := module_isExponentTwo
    symm
    calc
      P.underlying + P.cliffordPlus =
          (P.underlying + P.cliffordPlus) +
            (P.cliffordMinus + P.cliffordMinus) := by
              rw [h₂ P.cliffordMinus, add_zero]
      _ = (P.underlying + P.cliffordPlus + P.cliffordMinus) +
            P.cliffordMinus := by abel
      _ = P.cliffordMinus := by rw [hP, zero_add]
  apply BrauerPacket.ext
  · simp [packetOfCentralTitsMap]
  · simp [packetOfCentralTitsMap]
  · simp [packetOfCentralTitsMap, hMinus]

/-- Every balanced labelled packet is the evaluation packet of a unique
central Tits datum. -/
theorem existsUnique_centralTitsMap_of_isBalanced
    (P : BrauerPacket A) (hP : BrauerPacket.IsBalanced P) :
    ∃! t : D4CenterCharacter →ₗ[ZMod 2] A,
      packetOfCentralTitsMap t = P := by
  refine ⟨centralTitsMap P.underlying P.cliffordPlus,
    packetOfCentralTitsMap_centralTitsMap_of_isBalanced P hP, ?_⟩
  intro s hs
  apply packetOfCentralTitsMap_injective
  exact hs.trans
    (packetOfCentralTitsMap_centralTitsMap_of_isBalanced P hP).symm

/-- The linear root-datum layer is exactly the type of balanced labelled
packets. -/
def centralTitsEquivBalancedPacket :
    (D4CenterCharacter →ₗ[ZMod 2] A) ≃
      {P : BrauerPacket A // BrauerPacket.IsBalanced P} where
  toFun := fun t => ⟨packetOfCentralTitsMap t,
    packetOfCentralTitsMap_isBalanced t⟩
  invFun := fun P => centralTitsMap P.1.underlying P.1.cliffordPlus
  left_inv := centralTitsMap_of_values
  right_inv := by
    intro P
    apply Subtype.ext
    exact packetOfCentralTitsMap_centralTitsMap_of_isBalanced P.1 P.2

end RiemannResearch.E7.QuaternionTrialityPacket
