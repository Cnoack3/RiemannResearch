import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rational head certificate for the reciprocal compression

Source: independently developed exact rational certificate in the
user-directed RH continuation, 8 October 2026.

The physical constraints are orthogonality to the actual residue atoms at
conductors two and three. The accompanying paper proof supplies the infinite
weighted-Cauchy assembly and operator application; this module is deliberately
limited to the exact rational finite-head/full-tail numerical certificate.

The threshold is 3/7, the head contains the sites 3 through 36 inclusive,
and the entire remaining tail has displayed trace bound 37/832.
No RH or optimizer-decay hypothesis occurs in these finite declarations.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ReciprocalHeadCertificate

def weightOne (k : ℕ) : ℝ := -((k % 2 : ℕ) : ℝ)

def weightTwo (k : ℕ) : ℝ :=
  2 * (((k % 2 : ℕ) : ℝ) - ((k % 3 : ℕ) : ℝ))

def headGram11 : ℝ := ∑ i : Fin 34,
  (weightOne (i.val + 3)) ^ 2 /
    (((i.val + 3 : ℕ) : ℝ) ^ 2 * (3 / 7 - 1 / ((i.val + 3 : ℕ) : ℝ)))

def headGram22 : ℝ := ∑ i : Fin 34,
  (weightTwo (i.val + 3)) ^ 2 /
    (((i.val + 3 : ℕ) : ℝ) ^ 2 * (3 / 7 - 1 / ((i.val + 3 : ℕ) : ℝ)))

def headGram12 : ℝ := ∑ i : Fin 34,
  weightOne (i.val + 3) * weightTwo (i.val + 3) /
    (((i.val + 3 : ℕ) : ℝ) ^ 2 * (3 / 7 - 1 / ((i.val + 3 : ℕ) : ℝ)))

set_option maxRecDepth 4096 in
theorem normalized_head11_le : (4 / 7 : ℝ) * headGram11 ≤ 89 / 100 := by
  norm_num [headGram11, weightOne, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
theorem normalized_head22_le : (1 / 56 : ℝ) * headGram22 ≤ 4 / 25 := by
  norm_num [headGram22, weightTwo, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
theorem normalized_head12_sq_le : headGram12 ^ 2 / 98 ≤ 21 / 500 := by
  norm_num [headGram12, weightOne, weightTwo, Fin.sum_univ_succ]

/-- The residue bounds alone suffice; no independence is used. -/
theorem traceNumerator_le (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 2) :
    (4 / 7 : ℝ) * (a : ℝ) ^ 2 +
      (1 / 14 : ℝ) * ((a : ℝ) - (b : ℝ)) ^ 2 ≤ 9 / 14 := by
  interval_cases a <;> interval_cases b <;> norm_num

theorem tail_trace_constant :
    (9 / 14 : ℝ) / (36 * (3 / 7 - 1 / 37)) = 37 / 832 := by
  norm_num

/-- A signed cross term is bounded through its square. -/
theorem crossYoung (c x y : ℝ) (hc : c ^ 2 ≤ 21 / 500) :
    2 * c * x * y ≤ (3 / 50 : ℝ) * x ^ 2 + (7 / 10 : ℝ) * y ^ 2 := by
  have hcy := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
  nlinarith [sq_nonneg ((3 / 50 : ℝ) * x - c * y)]

/-- The full tail remains as an explicit input to this finite certificate. -/
theorem headTail_quadratic_le
    (A B c tail x y : ℝ)
    (hA : A ≤ 89 / 100) (hB : B ≤ 4 / 25)
    (hc : c ^ 2 ≤ 21 / 500)
    (htail : tail ≤ (37 / 832 : ℝ) * (x ^ 2 + y ^ 2)) :
    A * x ^ 2 + 2 * c * x * y + B * y ^ 2 + tail ≤
      (4137 / 4160 : ℝ) * (x ^ 2 + y ^ 2) := by
  have hAx := mul_le_mul_of_nonneg_right hA (sq_nonneg x)
  have hBy := mul_le_mul_of_nonneg_right hB (sq_nonneg y)
  have hcross := crossYoung c x y hc
  nlinarith [sq_nonneg y]

theorem headTail_coefficient_lt_one : (4137 / 4160 : ℝ) < 1 := by
  norm_num

theorem improved_secondMoment_cap : (3 / 7 : ℝ) ^ 2 = 9 / 49 := by
  norm_num

theorem improved_secondMoment_cap_lt_three_sixteenths :
    (9 / 49 : ℝ) < 3 / 16 := by
  norm_num

end RiemannResearch.RH.ReciprocalHeadCertificate
