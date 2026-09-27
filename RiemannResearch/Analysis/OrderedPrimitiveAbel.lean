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

/-- Dominated primitive variations control arbitrary simultaneous cutoffs.
The physical pairing itself need not be absolutely summable. -/
theorem primitive_abel_diagonal_partialSum_tendsto
    (B : ℕ → ℝ) (F : ℕ → ℕ → ℝ) (f D : ℕ → ℝ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hD : Summable (fun k => |B (k + 1)| * D k))
    (hv : ∀ j k, |F j k - F j (k + 1)| ≤ D k)
    (hp : ∀ k, Tendsto (fun j => F j k) atTop (𝓝 (f k)))
    (hend : Tendsto (fun j => B (N j) * F j (N j)) atTop (𝓝 0)) :
    Tendsto (fun j => ∑ k ∈ Finset.range (N j),
      (B (k + 1) - B k) * F j k) atTop
      (𝓝 (-B 0 * f 0 + ∑' k, B (k + 1) * (f k - f (k + 1)))) := by
  let T (j k : ℕ) : ℝ :=
    if k ∈ Finset.range (N j) then
      B (k + 1) * (F j k - F j (k + 1)) else 0
  have hD0 (k : ℕ) : 0 ≤ D k :=
    (abs_nonneg (F 0 k - F 0 (k + 1))).trans (hv 0 k)
  have hpoint (k : ℕ) : Tendsto (fun j => T j k) atTop
      (𝓝 (B (k + 1) * (f k - f (k + 1)))) := by
    apply (((hp k).sub (hp (k + 1))).const_mul (B (k + 1))).congr'
    filter_upwards [hN.eventually (eventually_ge_atTop (k + 1))] with j hj
    have hmem : k ∈ Finset.range (N j) := Finset.mem_range.mpr (Nat.lt_of_succ_le hj)
    simp only [T, if_pos hmem]
  have hmajor : ∀ᶠ j in atTop, ∀ k, ‖T j k‖ ≤ |B (k + 1)| * D k := by
    apply Eventually.of_forall
    intro j k
    by_cases hk : k ∈ Finset.range (N j)
    · simp only [T, if_pos hk, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hv j k) (abs_nonneg _)
    · simp only [T, if_neg hk, norm_zero]
      exact mul_nonneg (abs_nonneg _) (hD0 k)
  have ht := tendsto_tsum_of_dominated_convergence hD hpoint hmajor
  have he (j : ℕ) : (∑' k, T j k) =
      ∑ k ∈ Finset.range (N j), B (k + 1) * (F j k - F j (k + 1)) := by
    rw [tsum_eq_sum (s := Finset.range (N j))
      (by intro k hk; simp only [T, if_neg hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [T, if_pos hk]
  simp only [he] at ht
  simp_rw [boundedPrimitive_abel_identity]
  simpa only [zero_sub, neg_mul] using
    (hend.sub ((hp 0).const_mul (B 0))).add ht

end RiemannResearch.Analysis
