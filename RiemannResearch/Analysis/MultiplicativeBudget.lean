/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite multiplicative budgets

Elementary product and recurrence estimates used in the prime-power
energy-budget transfer. All one-step bounds remain explicit hypotheses.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.MultiplicativeBudget

theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∏ i ∈ s, (1 + a i)) ≤ Real.exp (∑ i ∈ s, a i) := by
  calc
    _ ≤ ∏ i ∈ s, Real.exp (a i) :=
      Finset.prod_le_prod (fun i hi => by linarith [ha i hi])
        (fun i _ => by simpa only [add_comm] using Real.add_one_le_exp (a i))
    _ = _ := (Real.exp_sum s a).symm

theorem prod_one_add_mul_le_exp {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (C B : ℝ) (hC : 0 ≤ C) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hbudget : ∑ i ∈ s, w i ≤ B) :
    (∏ i ∈ s, (1 + C * w i)) ≤ Real.exp (C * B) := by
  calc
    _ ≤ Real.exp (∑ i ∈ s, C * w i) :=
      prod_one_add_le_exp_sum s _ (fun i hi => mul_nonneg hC (hw i hi))
    _ = Real.exp (C * ∑ i ∈ s, w i) := by rw [Finset.mul_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget hC)

/-- An arbitrary sequence obeying the stated one-step bounds obeys the
finite product bound. No positivity assumption on intermediate E is needed. -/
theorem energy_le_initial_mul_prod (E w : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hw : ∀ n, 0 ≤ w n)
    (hstep : ∀ n, E (n + 1) ≤ (1 + C * w n) * E n) (N : ℕ) :
    E N ≤ E 0 * ∏ n ∈ Finset.range N, (1 + C * w n) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        _ ≤ (1 + C * w N) * E N := hstep N
        _ ≤ (1 + C * w N) *
            (E 0 * ∏ n ∈ Finset.range N, (1 + C * w n)) :=
          mul_le_mul_of_nonneg_left ih
            (add_nonneg (by norm_num) (mul_nonneg hC (hw N)))
        _ = _ := by rw [Finset.prod_range_succ]; ring

/-- A finite total weight controls the energy exponentially. -/
theorem energy_le_exp_of_sum_le (E w : ℕ → ℝ) (C B : ℝ)
    (hE : 0 ≤ E 0) (hC : 0 ≤ C) (hw : ∀ n, 0 ≤ w n)
    (hstep : ∀ n, E (n + 1) ≤ (1 + C * w n) * E n)
    (N : ℕ) (hbudget : ∑ n ∈ Finset.range N, w n ≤ B) :
    E N ≤ E 0 * Real.exp (C * B) :=
  (energy_le_initial_mul_prod E w C hC hw hstep N).trans
    (mul_le_mul_of_nonneg_left
      (prod_one_add_mul_le_exp (Finset.range N) w C B hC
        (fun n _ => hw n) hbudget) hE)

end RiemannResearch.Analysis.MultiplicativeBudget
