/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import RiemannResearch.RH.QPeriodicTailEnergy
import RiemannResearch.RH.ParetoCRTReciprocalEnergy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact comparisons between periodic blocks

Source: user-provided LCM block-squeeze proposal, 19 October 2026.
Refining the period of a fixed residual transfers energy from the omitted
tail to the displayed block. Only a change of residual can lower complete
energy; its signed mixed term is retained below.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoProbability
open Pareto

theorem periodic_qEnergy_first_tail_bounds (L : ℕ) (hL : 0 < L)
    (R : ℕ → ℝ) {C : ℝ} (hR : ∀ n, |R n| ≤ C)
    (hp : ∀ n, R (n + L) = R n) :
    crtReciprocalEnergy L R / zetaTwo +
        (1 - 1 / zetaTwo) * periodSquareEnergy L R / (L : ℝ)^2 ≤
      inversePowerMean 0 (fun n => R n^2) ∧
    inversePowerMean 0 (fun n => R n^2) ≤
      crtReciprocalEnergy L R / zetaTwo + periodSquareEnergy L R / (L : ℝ)^2 := by
  rw [periodic_qEnergy_first_tail L hL R hR hp]
  exact ⟨add_le_add le_rfl (periodicTailEnergy_bounds L hL R).1,
    add_le_add le_rfl (periodicTailEnergy_bounds L hL R).2⟩

theorem crtReciprocalEnergy_refinement (L K : ℕ) (hLK : L ≤ K) (R : ℕ → ℝ) :
    crtReciprocalEnergy K R = crtReciprocalEnergy L R +
      ∑ n ∈ Finset.Ico L K, R (n + 1)^2 / (n + 1 : ℝ)^2 := by
  have h := Finset.sum_Ico_eq_sub
    (fun n : ℕ => R (n + 1)^2 / (n + 1 : ℝ)^2) hLK
  have hf (J : ℕ) : crtReciprocalEnergy J R =
      ∑ n ∈ Finset.range J, R (n + 1)^2 / (n + 1 : ℝ)^2 := by
    simpa only [crtReciprocalEnergy, Nat.cast_add, Nat.cast_one] using
      (Fin.sum_univ_eq_sum_range
        (fun n : ℕ => R (n + 1)^2 / ((n + 1 : ℕ) : ℝ)^2) J)
  rw [hf K, hf L]
  linarith

/-- Reblocking a fixed residual supplies no variational period gain. -/
theorem periodicTailEnergy_refinement (L K : ℕ) (hL : 0 < L) (hK : 0 < K)
    (hLK : L ∣ K) (R : ℕ → ℝ) {C : ℝ} (hR : ∀ n, |R n| ≤ C)
    (hp : ∀ n, R (n + L) = R n) :
    periodicTailEnergy L R = periodicTailEnergy K R +
      (1 / zetaTwo) *
        ∑ n ∈ Finset.Ico L K, R (n + 1)^2 / (n + 1 : ℝ)^2 := by
  have hperiod : ∀ m n : ℕ, R (n + m * L) = R n := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih =>
        intro n
        rw [Nat.succ_mul, ← Nat.add_assoc, hp, ih]
  have hpK : ∀ n, R (n + K) = R n := by
    obtain ⟨m, rfl⟩ := hLK
    intro n
    simpa only [Nat.mul_comm] using hperiod m n
  have h1 := periodic_qEnergy_first_tail L hL R hR hp
  have h2 := periodic_qEnergy_first_tail K hK R hR hpK
  have h3 := crtReciprocalEnergy_refinement L K (Nat.le_of_dvd hK hLK) R
  rw [h3, add_div] at h2
  have halg : (1 / zetaTwo) *
      (∑ n ∈ Finset.Ico L K, R (n + 1)^2 / (n + 1 : ℝ)^2) =
      (∑ n ∈ Finset.Ico L K, R (n + 1)^2 / (n + 1 : ℝ)^2) / zetaTwo := by ring
  rw [halg]
  linarith

theorem periodicTailEnergy_mono_refinement (L K : ℕ) (hL : 0 < L) (hK : 0 < K)
    (hLK : L ∣ K) (R : ℕ → ℝ) {C : ℝ} (hR : ∀ n, |R n| ≤ C)
    (hp : ∀ n, R (n + L) = R n) :
    periodicTailEnergy K R ≤ periodicTailEnergy L R := by
  rw [periodicTailEnergy_refinement L K hL hK hLK R hR hp]
  have hs : 0 ≤ ∑ n ∈ Finset.Ico L K, R (n + 1)^2 / (n + 1 : ℝ)^2 :=
    Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  exact le_add_of_nonneg_right (mul_nonneg (one_div_pos.mpr zetaTwo_pos).le hs)

/-- Exact signed interaction when the residual changes on a common period. -/
theorem periodicTailEnergy_add (L : ℕ) (R U : ℕ → ℝ) :
    periodicTailEnergy L (fun n => R n + U n) = periodicTailEnergy L R +
      2 * (∑ a : Fin L, residuePowerWeight 0 L ((a.val : ℝ) + 1 + L) *
        R (a.val + 1) * U (a.val + 1)) + periodicTailEnergy L U := by
  unfold periodicTailEnergy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

end RiemannResearch.RH.ZetaTwoProbability
