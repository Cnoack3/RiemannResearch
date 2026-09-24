/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.BoundedPrimitiveAbel
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Ordered Abel pairing without absolute physical summability

Source: Section 1, steps 2--3 of the attached
`RH_Power_Damping_and_All_Dilation_Continuation_2026-09-24(1).md`.

The damped physical pairing may converge only in its natural order.  In
particular, an assertion `Summable` about that physical pairing would be a
stronger hypothesis than the mathematical argument supplies.  These lemmas
retain the natural-order limit and only use `tsum` for the absolutely
summable primitive-side variation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis

/-- Ordered Abel summation: no summability hypothesis is made about the
physical product `(B (k+1)-B k) * f k`. -/
theorem primitive_abel_partialSum_tendsto (B f : ℕ → ℝ)
    (hright : Summable (fun k => B (k + 1) * (f k - f (k + 1))))
    (hend : Tendsto (fun N => B N * f N) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, (B (k + 1) - B k) * f k)
      atTop (𝓝 (-B 0 * f 0 + ∑' k, B (k + 1) * (f k - f (k + 1)))) := by
  simp_rw [boundedPrimitive_abel_identity]
  simpa only [zero_sub, neg_mul] using
    (hend.sub_const (B 0 * f 0)).add hright.hasSum.tendsto_sum_nat

/-- A summable variation majorant suffices for the ordered pairing. -/
theorem primitive_abel_partialSum_tendsto_of_bound (B f D : ℕ → ℝ)
    (hD : Summable (fun k => |B (k + 1)| * D k))
    (hv : ∀ k, |f k - f (k + 1)| ≤ D k)
    (hend : Tendsto (fun N => B N * f N) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, (B (k + 1) - B k) * f k)
      atTop (𝓝 (-B 0 * f 0 + ∑' k, B (k + 1) * (f k - f (k + 1)))) := by
  apply primitive_abel_partialSum_tendsto B f _ hend
  apply Summable.of_norm_bounded hD
  intro k
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hv k) (abs_nonneg _)

/-- Damping may be removed on the primitive side even when none of the
physical pairings has been asserted absolutely summable. -/
theorem primitiveAbelPairing_tendsto
    (B : ℕ → ℝ) (F : ℕ → ℕ → ℝ) (f D : ℕ → ℝ)
    (hD : Summable (fun k => |B (k + 1)| * D k))
    (hv : ∀ᶠ j in atTop, ∀ k, |F j k - F j (k + 1)| ≤ D k)
    (hp : ∀ k, Tendsto (fun j => F j k) atTop (𝓝 (f k))) :
    Tendsto (fun j => -B 0 * F j 0 +
      ∑' k, B (k + 1) * (F j k - F j (k + 1))) atTop
      (𝓝 (-B 0 * f 0 + ∑' k, B (k + 1) * (f k - f (k + 1)))) := by
  apply ((hp 0).const_mul (-B 0)).add
  apply tendsto_tsum_of_dominated_convergence hD
  · intro k
    exact ((hp k).sub (hp (k + 1))).const_mul (B (k + 1))
  · filter_upwards [hv] with j hj
    intro k
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hj k) (abs_nonneg _)

end RiemannResearch.Analysis
