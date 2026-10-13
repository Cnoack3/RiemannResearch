/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Positive quadratic detector budgets

Source: scalar deductions from the supplied Pareto parity endpoint continuation,
13 October 2026. This file retains the detector's square and proves that its
positive quadratic lower iteration is still a closed endpoint for zero energy.
-/

namespace RiemannResearch.Analysis
theorem quadratic_detector_strict_budget {x d c a : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hd : 0 < d)
    (hq : c * d + a * x ^ 2 ≤ x) :
    c * d + a * (c * d) ^ 2 < x := by
  have hcd : 0 < c * d := mul_pos hc hd
  have hbase : c * d ≤ x := by
    have hs : 0 ≤ a * x ^ 2 := mul_nonneg ha.le (sq_nonneg x)
    linarith
  have hx : 0 < x := lt_of_lt_of_le hcd hbase
  have hstrict : c * d < x := by
    have hs : 0 < a * x ^ 2 := mul_pos ha (sq_pos_of_pos hx)
    linarith
  have hsq : (c * d) ^ 2 < x ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hstrict) (add_pos hx hcd)]
  have hmul := mul_lt_mul_of_pos_left hsq ha
  linarith
theorem quadratic_detector_zero_of_budget {x d c a : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hd : 0 ≤ d)
    (hq : c * d + a * x ^ 2 ≤ x)
    (hu : x ≤ c * d + a * (c * d) ^ 2) : d = 0 := by
  by_contra hn
  have hp : 0 < d := lt_of_le_of_ne hd (Ne.symm hn)
  have hs := quadratic_detector_strict_budget hc ha hp hq
  linarith
end RiemannResearch.Analysis
