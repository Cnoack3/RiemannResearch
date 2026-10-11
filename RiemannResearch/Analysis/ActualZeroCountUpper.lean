/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Unconditional total-count and ordinate-mode bounds

The proved actual local Riemann--von Mangoldt bound is accumulated over unit
intervals. Every actual zero and its multiplicity is retained.
-/

noncomputable section
open Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem count_nat_le_of_local_bound (A : ℝ) (hA : 0 ≤ A)
    (hlocal : ∀ t : ℝ,
      (Ncount t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) (n : ℕ) :
    (Ncount 0 (n : ℝ) : ℝ) ≤ A * (n : ℝ) * Real.log ((n : ℝ) + 3) := by
  have hz : Ncount 0 0 = 0 := by
    have h := Ncount_add (a := 0) (b := 0) (c := 0) le_rfl le_rfl
    omega
  induction n with
  | zero => simp [hz]
  | succ n ih =>
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have hadd := Ncount_add (a := 0) (b := (n : ℝ)) (c := (n : ℝ) + 1)
        hn (by linarith)
      have hl : (Ncount (n : ℝ) ((n : ℝ) + 1) : ℝ) ≤
          A * Real.log ((n : ℝ) + 3) := by
        simpa only [abs_of_nonneg hn] using hlocal n
      have hlog : Real.log ((n : ℝ) + 3) ≤ Real.log ((n : ℝ) + 1 + 3) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Nat.cast_succ, hadd, Nat.cast_add]
      calc
        _ ≤ A * (n : ℝ) * Real.log ((n : ℝ) + 3) +
            A * Real.log ((n : ℝ) + 3) := add_le_add ih hl
        _ = A * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 3) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)

/-- An unconditional upper count bound with one constant for every T ≥ 9. -/
theorem exists_count_le_height_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 9 ≤ T →
      (Ncount 0 T : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨A, hA, hlocal⟩ := RvM.zeta_local_zero_count
  refine ⟨4 * A, by positivity, ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith
  let n : ℕ := Nat.floor T + 1
  have hnlo : T ≤ (n : ℝ) := by
    have h := Nat.lt_floor_add_one T
    dsimp [n]
    push_cast
    exact h.le
  have hnhi : (n : ℝ) ≤ T + 1 := by
    have h := Nat.floor_le hT0.le
    dsimp [n]
    push_cast
    linarith
  have hnT : (n : ℝ) ≤ 2 * T := by linarith
  have hlog : Real.log ((n : ℝ) + 3) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T * T) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul hT0.ne' hT0.ne']; ring
  have hcount : (Ncount 0 T : ℝ) ≤ (Ncount 0 (n : ℝ) : ℝ) := by
    exact_mod_cast Ncount_mono (a := 0) (b := T) (c := 0) (d := (n : ℝ))
      le_rfl hnlo
  calc
    _ ≤ A * (n : ℝ) * Real.log ((n : ℝ) + 3) := hcount.trans
      (count_nat_le_of_local_bound A (by linarith) hlocal n)
    _ ≤ (A * (2 * T)) * (2 * Real.log T) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hnT (by linarith)
      · exact hlog
      · exact Real.log_nonneg (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
      · positivity
    _ = _ := by ring

/-- Every actual ordinate character has modulus one; its total sum is bounded
by the actual multiplicity count at the same height. -/
theorem norm_ordinateSum_le_count (T u : ℝ) :
    ‖ordinateSum T u‖ ≤ (Ncount 0 T : ℝ) := by
  simpa only [ordinateSum, ZeroOrdinate.phase_norm, realSum_one] using
    norm_sum_le T (fun ρ => ZeroOrdinate.phase u ρ.im)

theorem exists_normalized_ordinate_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T u : ℝ, 9 ≤ T →
      ‖ordinateSum T u / (T : ℂ)‖ ≤ C * Real.log T := by
  obtain ⟨C, hC, hcount⟩ := exists_count_le_height_log
  refine ⟨C, hC, ?_⟩
  intro T u hT
  have hT0 : 0 < T := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  apply (div_le_iff₀ hT0).2
  calc
    _ ≤ (Ncount 0 T : ℝ) := norm_ordinateSum_le_count T u
    _ ≤ C * T * Real.log T := hcount T hT
    _ = _ := by ring

end RiemannResearch.Analysis.ActualZeroOrdinate
