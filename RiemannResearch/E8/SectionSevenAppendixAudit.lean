/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD

/-!
# Section 7 and Appendix arithmetic

Finite arithmetic printed in Section 7 and Appendix A of the user-provided
5 August 2026 E8 Serre II manuscript. These declarations do not verify the
reported GAP subgroup enumeration.
-/

namespace RiemannResearch.E8

/-- The count, orbit-cardinality, and binary-icosahedral order arithmetic
printed in Section 7 and Appendix A. -/
theorem sectionSevenAppendix_arithmetic :
    (2880 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 ∧
      313 - 10 = 303 ∧
      150 + 153 = 303 ∧
      5 + 5 + 1 + 1 = 12 ∧
      120 / 12 + 120 / 120 = 11 ∧
      120 / 20 + 120 / 24 = 11 ∧
      24 * 20 / 4 = 120 := by
  norm_num

/-- The full-Weyl and five survivor-envelope Bezout identities, together
with the five corresponding gcd computations. -/
theorem sectionSevenAppendix_bezout_and_gcd :
    ((-1417 : ℤ) * 135 + 16 * 11200 + 12096 = 1) ∧
      ((-73 : ℤ) * 135 - 2 * 1120 + 12096 = 1) ∧
      ((15 : ℤ) * 15 - 5 * 1120 + 5376 = 1) ∧
      ((-17 : ℤ) * 135 - 2 * 1120 + 4536 = 1) ∧
      ((-57 : ℤ) * 135 - 2 * 40 + 7776 = 1) ∧
      ((13 : ℤ) * 25 - 9 * 36 = 1) ∧
      Nat.gcd (Nat.gcd 135 1120) 12096 = 1 ∧
      Nat.gcd (Nat.gcd 15 1120) 5376 = 1 ∧
      Nat.gcd (Nat.gcd 135 1120) 4536 = 1 ∧
      Nat.gcd (Nat.gcd 135 40) 7776 = 1 ∧
      Nat.gcd 25 36 = 1 := by
  norm_num

end RiemannResearch.E8
