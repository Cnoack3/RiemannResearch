/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Uniform power-logarithm bounds from dyadic increments

An elementary dyadic induction retaining a finite initial interval.
The intended consumer is the height-window assembly in
ActualSelbergDyadicAssembly. No zero-density estimate is assumed here
except through the displayed increment hypothesis of the general theorem.
-/

noncomputable section
namespace RiemannResearch.Analysis

/-- A monotone count is controlled by its dyadic increments and its finite head. -/
theorem bound_of_dyadic_power_log
    (F : ℝ → ℝ) {H D K p r : ℝ}
    (hH : 1 < H) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hmono : Monotone F) (hhead : F (2 * H) ≤ K * Real.log H)
    (hscale : (2 : ℝ) ^ (-p) ≤ r) (hcontract : K * r + D ≤ K)
    (hwindow : ∀ T : ℝ, 2 * H ≤ T →
      F T - F (T / 2) ≤ D * T ^ p * Real.log T) :
    ∀ T : ℝ, H ≤ T → F T ≤ K * T ^ p * Real.log T := by
  have hH0 : 0 < H := by linarith
  have hsmall : ∀ T : ℝ, H ≤ T → T ≤ 2 * H →
      F T ≤ K * T ^ p * Real.log T := by
    intro T hT hThi
    have hT1 : 1 ≤ T := (le_of_lt hH).trans hT
    have hpow : 1 ≤ T ^ p := Real.one_le_rpow hT1 hp
    have hlog : 0 ≤ Real.log H := (Real.log_pos hH).le
    calc
      F T ≤ F (2 * H) := hmono hThi
      _ ≤ K * Real.log H := hhead
      _ ≤ (K * T ^ p) * Real.log T := by
        exact mul_le_mul
          (by nlinarith : K ≤ K * T ^ p)
          (Real.log_le_log hH0 hT) hlog
          (mul_nonneg hK (Real.rpow_nonneg (by linarith) _))
  have hind : ∀ n : ℕ, ∀ T : ℝ, H ≤ T → T ≤ H * 2 ^ n →
      F T ≤ K * T ^ p * Real.log T := by
    intro n
    induction n with
    | zero =>
        intro T hT hu
        apply hsmall T hT
        simpa using (hu.trans (by nlinarith : H * (2 : ℝ) ^ 0 ≤ 2 * H))
    | succ n ih =>
        intro T hT hu
        by_cases hs : T ≤ 2 * H
        · exact hsmall T hT hs
        have hbig : 2 * H ≤ T := (lt_of_not_ge hs).le
        have hhalf : H ≤ T / 2 := by linarith
        have hhalfhi : T / 2 ≤ H * 2 ^ n := by
          rw [pow_succ] at hu
          linarith
        have hi := ih (T / 2) hhalf hhalfhi
        have hw := hwindow T hbig
        have hT0 : 0 < T := hH0.trans_le hT
        have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        have hhalfpos : 0 < T / 2 := by positivity
        have hloghalf : Real.log (T / 2) ≤ Real.log T :=
          Real.log_le_log hhalfpos (by linarith)
        have hpow : (T / 2) ^ p = T ^ p * (2 : ℝ) ^ (-p) := by
          rw [div_eq_mul_inv, Real.mul_rpow hT0.le (by positivity),
            Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        have hscale' : K * (T / 2) ^ p ≤ K * r * T ^ p := by
          rw [hpow]
          nlinarith [mul_le_mul_of_nonneg_left hscale
            (mul_nonneg hK (Real.rpow_nonneg hT0.le p))]
        have hi' : F (T / 2) ≤ K * r * T ^ p * Real.log T := by
          apply hi.trans
          exact (mul_le_mul_of_nonneg_left hloghalf
            (mul_nonneg hK (Real.rpow_nonneg hhalfpos.le p))).trans
            (mul_le_mul_of_nonneg_right hscale' hlog)
        have hc := mul_le_mul_of_nonneg_right hcontract
          (mul_nonneg (Real.rpow_nonneg hT0.le p) hlog)
        nlinarith
  intro T hT
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near
    ((one_le_div hH0).mpr hT) (show (1 : ℝ) < 2 by norm_num)
  apply hind (n + 1) T hT
  exact ((div_lt_iff₀ hH0).mp hn').le.trans_eq (mul_comm _ _)

end RiemannResearch.Analysis
