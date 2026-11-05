/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimeSubtreeBudget

/-! # Simultaneous saturation of finite carry digits

One integer immediately before any common multiple attains every digit upper
bound at once. A period supremum of an edgewise nonnegative cost therefore
recovers its entire unlocalized cost exactly. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeSubtreeBudget

private theorem common_pred_mod {r L : ℕ} (hr : 0 < r) (hL : 0 < L) (hd : r ∣ L) :
    (L - 1) % r = r - 1 := by
  obtain ⟨k, rfl⟩ := hd
  cases k with
  | zero => simp at hL
  | succ k =>
    rw [Nat.mul_succ, show r * k + r - 1 = r * k + (r - 1) by omega, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : r - 1 < r)]

/-- The residue class minus one saturates the digit on each edge dividing its period. -/
theorem stepDigit_common_pred {r L : ℕ} (hr : 1 < r) (hL : 0 < L) (hd : r ∣ L) :
    stepDigit r (L - 1) = ((r - parent r : ℕ) : ℝ) := by
  obtain ⟨hp, hlt, hd'⟩ := parent_spec r hr
  rw [stepDigit, common_pred_mod (by omega) hL hd, common_pred_mod hp hL (hd'.trans hd),
    Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_sub (by omega : 1 ≤ parent r),
    Nat.cast_sub hlt.le]
  ring

/-- Exact worst-site value of a sum with nonnegative edge weights, attained
simultaneously at the last site of the chosen period. -/
theorem weighted_digit_saturation (w : ℕ → ℝ) (H L : ℕ) (hL : 0 < L)
    (hd : ∀ r ∈ Finset.Icc 2 H, r ∣ L) (hw : ∀ r ∈ Finset.Icc 2 H, 0 ≤ w r) :
    (∀ n : ℕ, ∑ r ∈ Finset.Icc 2 H, stepDigit r n * w r ≤
      ∑ r ∈ Finset.Icc 2 H, ((r - parent r : ℕ) : ℝ) * w r) ∧
    (∑ r ∈ Finset.Icc 2 H, stepDigit r (L - 1) * w r =
      ∑ r ∈ Finset.Icc 2 H, ((r - parent r : ℕ) : ℝ) * w r) := by
  constructor
  · intro n
    apply Finset.sum_le_sum
    intro r hr
    exact mul_le_mul_of_nonneg_right (digit_bounds (Finset.mem_Icc.mp hr).1 n).2 (hw r hr)
  · apply Finset.sum_congr rfl
    intro r hr
    rw [stepDigit_common_pred (Finset.mem_Icc.mp hr).1 hL (hd r hr)]

end RiemannResearch.RH.QPrimeSubtreeBudget
