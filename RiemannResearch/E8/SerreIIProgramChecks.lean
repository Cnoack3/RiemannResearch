/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib
import RiemannResearch.GroupTheory.CoprimeRestriction

/-!
# Checks for the 5 August 2026 E8 Serre II program

This module records finite arithmetic and one chamber-normalization
counterexample for the exact packet degrees printed in the 5 August 2026
manuscript. It deliberately does not infer the existence of the asserted
splitting fields, subgroup embeddings, or nonabelian descent operations.

The manuscript's Theorem 3.2 chooses an arbitrary regular cocharacter and
claims that changing its sign if necessary gives the displayed
length-plus-descent formula. In type A2, the simple coroot has positive-root
pairings 2, -1, and 1. It is regular, but neither it nor its negative has both
simple-root pairings positive. Thus sign alone does not normalize a chamber.
-/

namespace RiemannResearch.E8

/-- The A2 positive-root pairings of the simple coroot are nonzero,
but neither its simple-root signs nor their negatives are all positive. -/
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
