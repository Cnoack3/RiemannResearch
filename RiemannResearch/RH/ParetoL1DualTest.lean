/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ThresholdHilbertL1
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Bounded physical dual tests for the full Pareto L1 norm

Source: the checked Pareto parity continuation of 13 October 2026,
preserved in source commit 3e698b7e48af90aae6d91bb159333f83cbb8ec35.
This statement and proof are recovered without changing the underlying norm.
The application to the explicit first-point sign test belongs to
ParetoProjectionOvershoot. No arithmetic convergence estimate is assumed here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

theorem inner_le_l1_of_sequence_abs_le_one (f h : ThresholdHilbert)
    (hh : ∀ k, |hilbertSequence h k| ≤ 1) :
    inner ℝ f h ≤ hilbertL1Norm f := by
  rw [hilbert_inner_weighted]
  unfold paretoInner hilbertL1Norm
  apply Summable.tsum_le_tsum
  · intro k
    apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg k)
    calc
      hilbertSequence f k * hilbertSequence h k ≤
          |hilbertSequence f k * hilbertSequence h k| := le_abs_self _
      _ = |hilbertSequence f k| * |hilbertSequence h k| := abs_mul _ _
      _ ≤ |hilbertSequence f k| := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hh k) (abs_nonneg (hilbertSequence f k))
  · exact weighted_product_summable_of_square
      (hilbertSequence_square_summable f) (hilbertSequence_square_summable h)
  · exact hilbertL1Norm_summable f

end RiemannResearch.RH.Pareto
