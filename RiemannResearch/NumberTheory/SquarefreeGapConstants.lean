/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact certificates for proposed squarefree-gap constant repairs

Source: Kumchev et al., arXiv:2211.09975v3, Sections 5 and 6.
These are rational arithmetic certificates only. In particular, the
analytic estimates which feed the final sieve sums are not proved here.
-/

namespace RiemannResearch.NumberTheory.SquarefreeGapConstants

/-- Rational certificates for the corrected cluster and sum coefficients.
The cubed comparison certifies the positive cube-root calculation needed
for the coefficient 0.01694 without floating-point evaluation. -/
theorem repaired_coefficients :
    (791 / 1000 : ℝ) ^ 3 < 99 / 200 ∧
    (209 / 200 : ℝ) ^ 6 / (791 / 1000) < 16464 / 10000 ∧
    (9 / 62 : ℝ) < 1452 / 10000 ∧
    (16464 / 10000 : ℝ) * (1452 / 10000) < 2391 / 10000 ∧
    ((4782 / 10000 : ℝ) / (8 / 3)) ^ 3 *
      ((1002 / 1000 : ℝ) * (17 / 100)) ^ 4 < (1694 / 100000) ^ 3 ∧
    2 * (32928 / 10000 : ℝ) * (2023 / 10000) < 13323 / 10000 ∧
    2 * (32928 / 10000 : ℝ) * (237 / 1000) < 15608 / 10000 := by
  norm_num

/-- All three changed coefficients in the final sigma formulas
are bounded by 1.101 times their original values. -/
theorem coefficient_inflation :
    (3388 / 100000 : ℝ) ≤ (1101 / 1000) * (308 / 10000) ∧
    (13323 / 10000 : ℝ) ≤ (1101 / 1000) * (12105 / 10000) ∧
    (15608 / 10000 : ℝ) ≤ (1101 / 1000) * (14182 / 10000) := by
  norm_num

/-- Corrected arithmetic totals for the two cases of Section 6.1.
The component estimates themselves remain separate proof obligations. -/
theorem repaired_sieve_totals :
    (1101 / 1000 : ℝ) * (1034 / 10000) + 548 / 10000 +
      (1101 / 1000) * (1148 / 10000) + 1642 / 10000 + 9 / 10000 <
        4602 / 10000 ∧
    -(595 / 10000 : ℝ) + 4523 / 10000 + 1461 / 10000 + 4602 / 10000 =
        9991 / 10000 ∧
    (1101 / 1000 : ℝ) * (2378 / 10000) + 2189 / 10000 -
      59 / 1000 + 9 / 10000 < 4227 / 10000 ∧
    -(595 / 10000 : ℝ) + 4523 / 10000 + 1797 / 10000 + 4227 / 10000 =
        9952 / 10000 := by
  norm_num

/-- Both repaired arithmetic margins are adequate once h is at least 2000. -/
theorem repaired_margins {h : ℝ} (hh : 2000 ≤ h) :
    (9991 / 10000 : ℝ) < 1 - 1 / h ∧
    (9952 / 10000 : ℝ) < 1 - 1 / h := by
  have hrec : 1 / h ≤ (1 / 2000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hh
  constructor <;> linarith

end RiemannResearch.NumberTheory.SquarefreeGapConstants
