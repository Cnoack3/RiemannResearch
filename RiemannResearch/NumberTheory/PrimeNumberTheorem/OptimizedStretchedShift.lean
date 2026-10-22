/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Elementary one-step shift control for the optimized stretched profile.
This is a real-variable lemma and assumes no arithmetic estimate. -/

noncomputable section
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- If z^11 = s log s and the cutoff is z^10, its profile changes by at
most 2(log s+1), once the displayed finite size conditions hold. -/
theorem optimized_stretched_shift_of_pow (s z v : ℝ)
    (hs : 6 ≤ s) (hz : 1 ≤ z) (hzpow : z ^ 11 = s * Real.log s)
    (hh : 2 * (Real.log s + 1) ≤ z)
    (hvdef : v = s - z ^ 10 - Real.log 2) (hv : s / 2 ≤ v) :
    0 ≤ v ∧
      z - (v * Real.log v) ^ ((1 : ℝ) / 11) ≤ 2 * (Real.log s + 1) := by
  have hs0 : 0 < s := by linarith
  have hv0 : 0 < v := by linarith
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hz0 : 0 ≤ z := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hz10 : 1 ≤ z ^ 10 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hz 10
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hs0 hv0)
  rw [Real.log_div hs0.ne' hv0.ne'] at hlogratio
  have hscaled := mul_le_mul_of_nonneg_left hlogratio hv0.le
  have he : v * (s / v - 1) = s - v := by field_simp <;> ring
  rw [he] at hscaled
  have hdiscrep :
      s * Real.log s - v * Real.log v ≤ (s - v) * (Real.log s + 1) := by
    nlinarith
  have hgap : s - v ≤ 2 * z ^ 10 := by
    rw [hvdef]
    nlinarith
  have hgapscaled := mul_le_mul_of_nonneg_right hgap
    (show 0 ≤ Real.log s + 1 by linarith)
  let h : ℝ := 2 * (Real.log s + 1)
  have hh0 : 0 ≤ h := by dsimp [h]; linarith
  have hhZ : h ≤ z := hh
  have hb0 : 0 ≤ z - h := sub_nonneg.mpr hhZ
  have hbZ : z - h ≤ z := by linarith
  have hlow : z ^ 11 - h * z ^ 10 ≤ v * Real.log v := by
    dsimp [h]
    nlinarith [hdiscrep, hgapscaled]
  have hp : (z - h) ^ 10 ≤ z ^ 10 := pow_le_pow_left₀ hb0 hbZ 10
  have hpow : (z - h) ^ 11 ≤ z ^ 11 - h * z ^ 10 := by
    calc
      _ = (z - h) ^ 10 * (z - h) := by rw [pow_succ]
      _ ≤ z ^ 10 * (z - h) := mul_le_mul_of_nonneg_right hp hb0
      _ = _ := by ring
  have hr := Real.rpow_le_rpow (pow_nonneg hb0 11) (hpow.trans hlow)
    (by norm_num : (0 : ℝ) ≤ 1 / 11)
  have hroot : ((z - h) ^ 11) ^ ((1 : ℝ) / 11) = z - h := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0]
    norm_num
  rw [hroot] at hr
  refine ⟨hv0.le, ?_⟩
  dsimp [h] at hr
  linarith

theorem optimized_stretched_shift (s : ℝ)
    (hs : 6 ≤ s)
    (hz : 1 ≤ (s * Real.log s) ^ ((1 : ℝ) / 11))
    (hh : 2 * (Real.log s + 1) ≤ (s * Real.log s) ^ ((1 : ℝ) / 11))
    (hv : s / 2 ≤ s - ((s * Real.log s) ^ ((1 : ℝ) / 11)) ^ 10 - Real.log 2) :
    let v := s - ((s * Real.log s) ^ ((1 : ℝ) / 11)) ^ 10 - Real.log 2
    0 ≤ v ∧ (s * Real.log s) ^ ((1 : ℝ) / 11) -
      (v * Real.log v) ^ ((1 : ℝ) / 11) ≤ 2 * (Real.log s + 1) := by
  have hprod : 0 ≤ s * Real.log s := mul_nonneg (by linarith)
    (Real.log_nonneg (by linarith))
  have hpow : ((s * Real.log s) ^ ((1 : ℝ) / 11)) ^ 11 = s * Real.log s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hprod]
    norm_num
  exact optimized_stretched_shift_of_pow s
    ((s * Real.log s) ^ ((1 : ℝ) / 11))
    (s - ((s * Real.log s) ^ ((1 : ℝ) / 11)) ^ 10 - Real.log 2)
    hs hz hpow hh rfl hv

end RiemannResearch.NumberTheory.PrimeNumberTheorem
