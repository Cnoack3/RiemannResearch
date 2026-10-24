/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Explicit exponential sampling heights

Source: user-provided constructive approximants handoff, 24 October 2026,
Section 5. This module proves the scalar scheduling argument. The horizontal
energy and uniform Landau bounds are explicit provider hypotheses; no theorem
here proves Selberg's density estimate or supplies effective Landau constants.
The actual RH consumer is inverse-Gram sampling in `RH/RamanujanZeroSignal`.
-/

namespace RiemannResearch.Analysis.ExplicitSamplingHeights

/-- Computable log heights. The weight w(j) is a certified integer upper
bound for the finite inverse-Gram budgets at stage j. -/
def logHeight (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => logHeight w j + 16 + (j + 1) * w (j + 1)

theorem logHeight_strictMono (w : ℕ → ℕ) : StrictMono (logHeight w) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [logHeight]
  omega

theorem logHeight_ge_weight (w : ℕ → ℕ) (j : ℕ) :
    j * w j ≤ logHeight w j := by
  cases j with
  | zero => simp [logHeight]
  | succ j => simp only [logHeight]; omega

theorem logHeight_ge_sixteen (w : ℕ → ℕ) {j : ℕ} (hj : 0 < j) :
    16 ≤ logHeight w j := by
  cases j with
  | zero => omega
  | succ j => simp only [logHeight]; omega

/-- A convenient elementary exponential majorant, valid without a large-M
cutoff. It retains the coefficient one in the handoff's error estimate. -/
theorem sq_le_exp_of_nonneg (M : ℝ) (hM : 0 ≤ M) : M ^ 2 ≤ Real.exp M := by
  have hq := Real.add_one_le_exp (M / 4)
  have he := Real.exp_pos (M / 4)
  have hp : (1 + M / 4) ^ 2 ≤ Real.exp (M / 4) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ Real.exp (M / 4) - (1 + M / 4) by linarith)
      (show 0 ≤ Real.exp (M / 4) + (1 + M / 4) by positivity)]
  have hm : M ≤ Real.exp (M / 4) ^ 2 := by
    nlinarith [sq_nonneg (M - 4)]
  have hs : M ^ 2 ≤ (Real.exp (M / 4) ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm)
      (show 0 ≤ Real.exp (M / 4) ^ 2 + M by positivity)]
  have hexp : (Real.exp (M / 4) ^ 2) ^ 2 = Real.exp M := by
    calc
      _ = (Real.exp (M / 4) * Real.exp (M / 4)) *
          (Real.exp (M / 4) * Real.exp (M / 4)) := by ring
      _ = Real.exp (M / 4 + M / 4) * Real.exp (M / 4 + M / 4) := by
        rw [Real.exp_add]
      _ = Real.exp ((M / 4 + M / 4) + (M / 4 + M / 4)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp M := by congr 1; ring
  rwa [hexp] at hs

theorem logHeight_budget_ratio (w : ℕ → ℕ) {j : ℕ} (hj : 0 < j)
    (R L : ℝ) (hR : R ≤ (w j : ℝ)) (hRL : R * L ≤ (w j : ℝ)) :
    R / (logHeight w j : ℝ) ≤ 1 / (j : ℝ) ∧
      (R * L) / (logHeight w j : ℝ) ≤ 1 / (j : ℝ) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hM : (0 : ℝ) < logHeight w j := by
    have h := logHeight_ge_sixteen w hj
    exact_mod_cast (show 0 < logHeight w j by omega)
  have hw : (j : ℝ) * (w j : ℝ) ≤ (logHeight w j : ℝ) := by
    exact_mod_cast logHeight_ge_weight w j
  constructor
  · apply (div_le_div_iff₀ hM hj').mpr
    nlinarith [mul_le_mul_of_nonneg_left hR hj'.le]
  · apply (div_le_div_iff₀ hM hj').mpr
    nlinarith [mul_le_mul_of_nonneg_left hRL hj'.le]

/-- The two analytic contributions at one logarithmic height. No fixed-D
Big-O is silently promoted to a uniform estimate. -/
theorem sampled_error_of_log_height
    (err A B R L M : ℝ) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hM : 0 < M)
    (hprovider : err ≤ A * R / M + B * R * L * M / Real.exp M) :
    err ≤ (A * R + B * R * L) / M := by
  have he : M / Real.exp M ≤ 1 / M := by
    apply (div_le_div_iff₀ (Real.exp_pos M) hM).mpr
    simpa only [one_mul, pow_two] using sq_le_exp_of_nonneg M hM.le
  have hmul := mul_le_mul_of_nonneg_left he
    (show 0 ≤ B * R * L by positivity)
  calc
    err ≤ A * R / M + B * R * L * M / Real.exp M := hprovider
    _ ≤ A * R / M + B * R * L / M := by
      simp only [div_eq_mul_inv] at hmul ⊢
      nlinarith
    _ = _ := by ring

/-- Certified integer budget bounds make the handoff's diagonal height
schedule quantitative. A=4*pi*C_0 and B=2*K recover its sampling constant. -/
theorem sampled_error_of_explicit_height_schedule
    (w : ℕ → ℕ) {j : ℕ} (hj : 0 < j)
    (err A B R L : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hwR : R ≤ (w j : ℝ)) (hwRL : R * L ≤ (w j : ℝ))
    (hprovider : err ≤ A * R / (logHeight w j : ℝ) +
      B * R * L * (logHeight w j : ℝ) / Real.exp (logHeight w j : ℝ)) :
    err ≤ (A + B) / (j : ℝ) := by
  have hM : (0 : ℝ) < logHeight w j := by
    have h := logHeight_ge_sixteen w hj
    exact_mod_cast (show 0 < logHeight w j by omega)
  have hbase := sampled_error_of_log_height err A B R L
    (logHeight w j) hA hB hR hL hM hprovider
  obtain ⟨h₁, h₂⟩ := logHeight_budget_ratio w hj R L hwR hwRL
  have ha := mul_le_mul_of_nonneg_left h₁ hA
  have hb := mul_le_mul_of_nonneg_left h₂ hB
  calc
    err ≤ (A * R + B * R * L) / (logHeight w j : ℝ) := hbase
    _ ≤ (A + B) / (j : ℝ) := by
      simp only [div_eq_mul_inv] at ha hb ⊢
      nlinarith

/-- Finite tolerance certificate after the analytic provider is valid. The
threshold and A,B must be effective to certify a specific early stage. -/
theorem sampled_error_le_tolerance
    (err A B j ε : ℝ) (hj : 0 < j)
    (herror : err ≤ (A + B) / j) (hstage : A + B ≤ ε * j) :
    err ≤ ε :=
  herror.trans ((div_le_iff₀ hj).mpr hstage)

theorem exponential_logHeight_strictMono (w : ℕ → ℕ) :
    StrictMono (fun j => Real.exp (logHeight w j : ℝ)) := by
  intro i j hij
  apply Real.exp_lt_exp.mpr
  exact_mod_cast logHeight_strictMono w hij

end RiemannResearch.Analysis.ExplicitSamplingHeights
