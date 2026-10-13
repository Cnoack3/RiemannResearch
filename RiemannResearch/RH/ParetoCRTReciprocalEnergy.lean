/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoNoiseSignal
import RiemannResearch.RH.ParetoCovariance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal-square first-period certificates for the actual Pareto norm

Source: user-provided CRT exact-head argument, 13 October 2026.
The complete periodic norm is the existing exact progression-weight sum.
This module bounds that complete sum by twice its finite reciprocal-square
certificate. No uniform coefficient bound or approximation is assumed proved.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem crt_progression_reciprocal_bound (L a : ℕ) (ha : 0 < a) (haL : a ≤ L) :
    progressionWeight L a ≤ 2 / (a : ℝ)^2 := by
  have hL : 0 < L := lt_of_lt_of_le ha haL
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haLR : (a : ℝ) ≤ L := by exact_mod_cast haL
  have htail : 1 / ((L : ℝ) * ((a : ℝ)+1)) ≤
      1 / ((a : ℝ) * ((a : ℝ)+1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right haLR (by positivity)
  have hatom : 1 / ((a : ℝ) * ((a : ℝ)+1)) ≤ 1 / (a : ℝ)^2 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h := progressionWeight_upper_one L a hL
  unfold positiveWeight at h
  calc
    progressionWeight L a ≤ 1 / (a : ℝ)^2 + 1 / (a : ℝ)^2 := by linarith
    _ = 2 / (a : ℝ)^2 := by ring

def crtReciprocalEnergy (L : ℕ) (R : ℕ → ℝ) : ℝ :=
  ∑ a : Fin L, (R (a.val+1))^2 / ((a.val+1 : ℕ) : ℝ)^2

theorem crtReciprocalEnergy_nonneg (L : ℕ) (R : ℕ → ℝ) :
    0 ≤ crtReciprocalEnergy L R := by
  exact Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem periodic_paretoInner_le_crtReciprocalEnergy
    (L : ℕ) (hL : 0 < L) (R : ℕ → ℝ) {C : ℝ}
    (hR : ∀ n, |R n| ≤ C) (hp : ∀ n, R (n + L) = R n) :
    paretoInner R R ≤ 2 * crtReciprocalEnergy L R := by
  rw [periodic_paretoInner L hL R hR hp]
  unfold crtReciprocalEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have h := mul_le_mul_of_nonneg_right
    (crt_progression_reciprocal_bound L (a.val+1) (by omega) (by omega))
    (sq_nonneg (R (a.val+1)))
  convert h using 1
  ring


theorem periodic_paretoError_le_crtReciprocalEnergy
    (L : ℕ) (hL : 0 < L) (F : ℕ → ℝ) {C : ℝ}
    (hF : ∀ n, |F n| ≤ C) (hp : ∀ n, F (n + L) = F n) :
    paretoError F ≤ 2 * crtReciprocalEnergy L (fun n => 1 - F n) := by
  exact periodic_paretoInner_le_crtReciprocalEnergy L hL
    (fun n => 1 - F n)
    (bounded_sub (C := 1) (by intro n; norm_num) hF)
    (by intro n; rw [hp])

/-- Exact initial zeros leave only the displayed first-period tail. -/
theorem crtReciprocalEnergy_eq_tail (M L : ℕ) (R : ℕ → ℝ)
    (hhead : ∀ n, 0 < n → n ≤ M → R n = 0) :
    crtReciprocalEnergy L R =
      ∑ a : Fin L, if M < a.val + 1 then
        (R (a.val + 1)) ^ 2 / ((a.val + 1 : ℕ) : ℝ) ^ 2 else 0 := by
  unfold crtReciprocalEnergy
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : M < a.val + 1
  · simp [ha]
  · simp [ha, hhead (a.val + 1) (by omega) (by omega)]

end
end RiemannResearch.RH.Pareto
