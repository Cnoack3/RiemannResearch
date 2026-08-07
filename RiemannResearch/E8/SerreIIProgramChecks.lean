/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib
import RiemannResearch.AlgebraicGeometry.PointFieldIndexOne
import RiemannResearch.GroupTheory.CoprimeRestriction

/-!
# Checks for the 5 August 2026 E8 Serre II program

This module records finite arithmetic and one chamber-normalization
counterexample for the exact packet degrees printed in the 5 August 2026
manuscript. It deliberately does not infer the existence of the asserted
splitting fields, subgroup embeddings, or nonabelian descent operations.

The intended convention in Theorem 3.2 is to choose the regular cocharacter
in the chamber determined by the fixed Borel; changing its sign then selects
the attracting convention. The A2 calculation below records why this chamber
choice matters: if one instead starts with an arbitrary regular cocharacter,
sign alone need not normalize it. This does not challenge the theorem under
the chosen-chamber convention.
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


/-- For a literal arbitrary-cocharacter reading, the A2 positive-root
pairings are nonzero while neither sign is positive on both simple roots. -/
theorem a2Coroot_sign_normalization_counterexample :
    (2 : ℤ) ≠ 0 ∧ (-1 : ℤ) ≠ 0 ∧ 2 + (-1 : ℤ) ≠ 0 ∧
      ¬ (((0 : ℤ) < 2 ∧ (0 : ℤ) < -1) ∨
        ((0 : ℤ) < -2 ∧ (0 : ℤ) < 1)) := by
  norm_num

/-- The three stabilizer orders in PDF Theorem 5.16 have the stated
indices in the E8 Weyl group. -/
theorem serreIIProgram_fullWeylSubsystem_index_products :
    5160960 * 135 = 696729600 ∧
      62208 * 11200 = 696729600 ∧
      57600 * 12096 = 696729600 := by
  norm_num

/-- The degree-one cycle identity in PDF Corollary 5.17. -/
theorem serreIIProgram_threeSubsystem_bezout :
    (-1417 : ℤ) * 135 + 16 * 11200 + 12096 = 1 := by
  norm_num

/-- The three subsystem degrees in PDF Theorem 5.16 have gcd one. -/
theorem serreIIProgram_threeSubsystem_gcd :
    Nat.gcd (Nat.gcd 135 11200) 12096 = 1 := by
  norm_num

/-- The overlap and Sylow-five field degrees in PDF Proposition 6.7. -/
theorem serreIIProgram_a8Gauge_field_degrees :
    20160 / 192 = 105 ∧ 20160 / 5 = 4032 := by
  norm_num

/-- An integral Bezout certificate for the three degrees in PDF Proposition 6.7. -/
theorem serreIIProgram_a8Gauge_bezout :
    (-3226 : ℤ) * 15 + 1613 * 35 - 2 * 4032 = 1 := by
  norm_num

/-- The three degrees in PDF Proposition 6.7 have gcd one. -/
theorem serreIIProgram_a8Gauge_gcd :
    Nat.gcd (Nat.gcd 15 35) 4032 = 1 := by
  norm_num

/-- The additive restriction--corestriction shadow of PDF Proposition 6.7. -/
theorem eq_zero_of_serreIIProgram_a8Gauge_annihilators
    {A : Type*} [AddCommGroup A] {x : A}
    (h15 : 15 • x = 0) (h35 : 35 • x = 0) (h4032 : 4032 • x = 0) :
    x = 0 := by
  have h5 : 5 • x = 0 := by
    apply (nsmul_eq_zero_iff_of_coprime
      (by norm_num : Nat.Coprime 3 7)).mp
    constructor
    · rw [← mul_nsmul]
      norm_num
      exact h15
    · rw [← mul_nsmul]
      norm_num
      exact h35
  exact (nsmul_eq_zero_iff_of_coprime
    (by norm_num : Nat.Coprime 5 4032)).mp ⟨h5, h4032⟩

/-- All five displayed Bezout identities in PDF Theorem 6.9. -/
theorem serreIIProgram_survivorEnvelope_bezout :
    (-73 : ℤ) * 135 - 2 * 1120 + 12096 = 1 ∧
      (15 : ℤ) * 15 - 5 * 1120 + 5376 = 1 ∧
      (-17 : ℤ) * 135 - 2 * 1120 + 4536 = 1 ∧
      (-57 : ℤ) * 135 - 2 * 40 + 7776 = 1 ∧
      (13 : ℤ) * 25 - 9 * 36 = 1 := by
  norm_num

/-- The five degree rows in PDF Theorem 6.9 have gcd one. -/
theorem serreIIProgram_survivorEnvelope_gcd :
    Nat.gcd (Nat.gcd 135 1120) 12096 = 1 ∧
      Nat.gcd (Nat.gcd 15 1120) 5376 = 1 ∧
      Nat.gcd (Nat.gcd 135 1120) 4536 = 1 ∧
      Nat.gcd (Nat.gcd 135 40) 7776 = 1 ∧
      Nat.gcd 25 36 = 1 := by
  norm_num

/-- The elementary order and index calculations in PDF Proposition 6.15. -/
theorem serreIIProgram_binaryIcosahedral_index_arithmetic :
    12 * 10 / 2 = 60 ∧ 24 * 20 / 4 = 120 ∧
      120 / 24 = 5 ∧ 120 / 20 = 6 := by
  norm_num

end RiemannResearch.E8
