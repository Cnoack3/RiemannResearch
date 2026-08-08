/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import RiemannResearch.AlgebraicGeometry.PointFieldIndexOne

/-!
# Sylow-local four-field splitting package

The finite point-field and prime-avoidance portion of the 5 August 2026 E8
Serre II program, separated from its independent numerical certificates.
-/

namespace RiemannResearch.E8

open RiemannResearch.AlgebraicGeometry

/-- The elementary prime-support step in PDF Theorem 2.2: a common divisor
of the Totaro degree and the three Sylow-local degrees must be one. -/
theorem serreIIProgram_fourField_gcd
    {d0 d2 d3 d5 : ℕ}
    (h0 : d0 ∣ 2880) (h2 : ¬ 2 ∣ d2) (h3 : ¬ 3 ∣ d3)
    (h5 : ¬ 5 ∣ d5) :
    Nat.gcd (Nat.gcd (Nat.gcd d0 d2) d3) d5 = 1 := by
  let g := Nat.gcd (Nat.gcd (Nat.gcd d0 d2) d3) d5
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hg5 : g ∣ d5 := Nat.gcd_dvd_right _ _
  have hg3 : g ∣ d3 :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hg2 : g ∣ d2 :=
    (Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
  have hg0 : g ∣ d0 :=
    (Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
  have hp2880 : p ∣ 2880 := hpg.trans (hg0.trans h0)
  have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 := by
    have hfac : 2880 = 2 ^ 6 * 3 ^ 2 * 5 := by norm_num
    rw [hfac] at hp2880
    rcases hp.dvd_mul.mp hp2880 with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · left
        exact ((Nat.dvd_prime (by norm_num)).mp
          (Nat.Prime.dvd_of_dvd_pow hp h)).resolve_left hp.ne_one
      · right; left
        exact ((Nat.dvd_prime (by norm_num)).mp
          (Nat.Prime.dvd_of_dvd_pow hp h)).resolve_left hp.ne_one
    · right; right
      exact ((Nat.dvd_prime (by norm_num)).mp h).resolve_left hp.ne_one
  rcases hp_cases with rfl | rfl | rfl
  · exact h2 (hpg.trans hg2)
  · exact h3 (hpg.trans hg3)
  · exact h5 (hpg.trans hg5)

/-- Lean-visible conclusion of PDF Theorem 2.2 at the finite point-field
interface. `primeAvoidance` records the co-p-closure and finite-descent input;
the theorem chooses the four displayed fields, proves their degree gcd is one,
and derives point-field index one from the full prime-local package. -/
def SylowLocalFourFieldConclusion
    (Extension : Type*) (isFinite : Extension → Prop)
    (degree : Extension → ℕ) (hasPoint : Extension → Prop) : Prop :=
  ∃ L0 L2 L3 L5,
    isFinite L0 ∧ isFinite L2 ∧ isFinite L3 ∧ isFinite L5 ∧
    hasPoint L0 ∧ hasPoint L2 ∧ hasPoint L3 ∧ hasPoint L5 ∧
    degree L0 ∣ 2880 ∧ ¬ 2 ∣ degree L2 ∧ ¬ 3 ∣ degree L3 ∧
    ¬ 5 ∣ degree L5 ∧
    Nat.gcd (Nat.gcd (Nat.gcd (degree L0) (degree L2))
      (degree L3)) (degree L5) = 1 ∧
    pointFieldIndex isFinite degree hasPoint = 1

/-- Conditional formalization of the complete logical content of PDF
Theorem 2.2 after its cited geometric inputs are expressed as actual finite
splitting fields. -/
theorem sylowLocalFourFieldSplittingPackage
    {Extension : Type*}
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (hasPoint : Extension → Prop)
    (totaroField : ∃ L, isFinite L ∧ hasPoint L ∧ degree L ∣ 2880)
    (primeAvoidance : ∀ p, p.Prime →
      ∃ L, isFinite L ∧ hasPoint L ∧ ¬ p ∣ degree L) :
    SylowLocalFourFieldConclusion Extension isFinite degree hasPoint := by
  obtain ⟨L0, hL0finite, hL0point, hL0degree⟩ := totaroField
  obtain ⟨L2, hL2finite, hL2point, hL2degree⟩ :=
    primeAvoidance 2 (by norm_num)
  obtain ⟨L3, hL3finite, hL3point, hL3degree⟩ :=
    primeAvoidance 3 (by norm_num)
  obtain ⟨L5, hL5finite, hL5point, hL5degree⟩ :=
    primeAvoidance 5 (by norm_num)
  refine ⟨L0, L2, L3, L5,
      hL0finite,
      hL2finite,
      hL3finite,
      hL5finite,
      hL0point,
      hL2point,
      hL3point,
      hL5point,
      hL0degree,
      hL2degree,
      hL3degree,
      hL5degree,
      ?_, ?_⟩
  · exact serreIIProgram_fourField_gcd
      hL0degree hL2degree hL3degree hL5degree
  · exact pointFieldIndex_eq_one_of_prime_avoidance
      isFinite degree hasPoint primeAvoidance

end RiemannResearch.E8
