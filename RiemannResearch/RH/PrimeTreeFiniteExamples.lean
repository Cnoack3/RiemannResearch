/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.NormNum

/-! # Finite arithmetic in the prime-prefix examples

Source: *Prime trees, fractional parts, and zeta zeros* (5 November 2026),
figures 1 and 2, and the Haar fit in §2. These rational checks evaluate the
finite-period examples directly. -/

namespace RiemannResearch.RH.PrimeTreeFiniteExamples

private def g (q n : ℕ) : ℚ := (n % q : ℕ) / (q : ℚ)
private def affine30 (n : ℕ) : ℚ := 11/30 + g 2 n / 15 + g 3 n / 10 + g 5 n / 6
private def raw30 (n : ℕ) : ℚ := g 2 n + g 3 n + g 5 n

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The complete period gives the advertised affine error and both mean carries. -/
theorem haar_period_thirty :
    (∑ n ∈ Finset.range 30, (g 30 n - affine30 n)^2) / 30 = 2/25 ∧
    (∑ n ∈ Finset.range 30, (⌊raw30 n⌋ : ℚ)) / 30 = 1/2 ∧
    (∑ n ∈ Finset.range 30, (⌊raw30 n - 2 * g 2 n⌋ : ℚ)) / 30 = 0 := by
  norm_num [Finset.sum_range_succ, affine30, raw30, g]

/-- The three refinements at the observation site 137. -/
theorem digits_at_137 :
    (137 % 2, 137 % 6, 137 % 30, 137 % 210) = (1, 5, 17, 137) ∧
    ((137 / 2) % 3, (137 / 6) % 5, (137 / 30) % 7) = (2, 2, 4) := by decide

/-- The four positive edge masses plus their exact omitted mass. -/
theorem first_chain_probability_boundary :
    (2/3 + 8/25 + 6/455 + 4/27313 : ℚ) + 1/14339325 = 1 ∧
    2 * (1/12415 : ℚ) / 2310 = 1/14339325 := by norm_num

/-- Repeated radices in §1 produce identical proposed inputs at two distinct residues. -/
theorem repeated_radix_example :
    (45 % 3, 45 % 5, 45 % 9) = (90 % 3, 90 % 5, 90 % 9) ∧ 45 % 135 ≠ 90 % 135 := by decide

end RiemannResearch.RH.PrimeTreeFiniteExamples
