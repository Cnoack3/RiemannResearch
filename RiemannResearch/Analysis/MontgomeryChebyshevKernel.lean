/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Squared Chebyshev kernel for a bounded band of nonzero gap phases

Normalize the Chebyshev polynomial at the zero phase. Squaring preserves
positivity, and the hyperbolic cosine formula gives an exponential envelope
over nonzero phases before aliasing.
-/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryFormFactor
open Polynomial.Chebyshev

/-- Square of a normalized Chebyshev filter. The denominator corresponds to zero phase. -/
def chebyshevResolvingKernel (n : ℕ) (t b : ℝ) : ℝ :=
  ((T ℝ (n : ℤ)).eval t / (T ℝ (n : ℤ)).eval b) ^ 2

private theorem chebyshev_eval_eq_cosh_arcosh (n : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    (T ℝ (n : ℤ)).eval b = Real.cosh ((n : ℝ) * Real.arcosh b) := by
  conv_lhs => rw [← Real.cosh_arcosh hb]
  simpa only [Int.cast_natCast] using T_real_cosh (Real.arcosh b) (n : ℤ)

theorem chebyshevResolvingKernel_at_base (n : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    chebyshevResolvingKernel n b b = 1 := by
  rw [chebyshevResolvingKernel, chebyshev_eval_eq_cosh_arcosh n hb]
  simp [(Real.cosh_pos _).ne']

/-- When the rescaled nonzero phase lies in the oscillation interval, squared
Chebyshev resolution decays exponentially with the polynomial degree. -/
theorem chebyshevResolvingKernel_le (n : ℕ) {t b : ℝ} (ht : |t| ≤ 1) (hb : 1 ≤ b) :
    chebyshevResolvingKernel n t b ≤ 4 * Real.exp (-2 * ((n : ℝ) * Real.arcosh b)) := by
  let u := (n : ℝ) * Real.arcosh b
  let a := (T ℝ (n : ℤ)).eval t
  have ha : |a| ≤ 1 := abs_eval_T_real_le_one (n : ℤ) ht
  have hc := Real.cosh_pos u
  have he := Real.exp_pos u
  have hce : Real.exp u ≤ 2 * Real.cosh u := by
    rw [Real.cosh_eq]
    linarith only [Real.exp_pos (-u)]
  rw [chebyshevResolvingKernel, chebyshev_eval_eq_cosh_arcosh n hb]
  change (a / Real.cosh u) ^ 2 ≤ 4 * Real.exp (-2 * u)
  calc
    _ = (|a| / Real.cosh u) ^ 2 := by rw [div_pow, div_pow, sq_abs]
    _ ≤ (1 / Real.cosh u) ^ 2 := (sq_le_sq₀ (by positivity) (by positivity)).2
      (div_le_div_of_nonneg_right ha hc.le)
    _ ≤ (2 / Real.exp u) ^ 2 := (sq_le_sq₀ (by positivity) (by positivity)).2
      ((div_le_div_iff₀ hc he).2 (by simpa only [one_mul] using hce))
    _ = _ := by
      rw [show -2 * u = -(u + u) by ring, Real.exp_neg, Real.exp_add]
      field_simp <;> ring

/-- The Chebyshev envelope on a nonzero normalized phase between the prescribed
gap floor and the first aliasing boundary. -/
theorem chebyshevResolvingKernel_cos_le (n : ℕ) {δ v : ℝ}
    (hδ : 0 ≤ δ) (hδπ : δ < Real.pi / 2) (hlo : δ ≤ |v|) (hhi : |v| ≤ Real.pi / 2) :
    chebyshevResolvingKernel n (Real.cos v / Real.cos δ) (Real.cos δ)⁻¹ ≤
      4 * Real.exp (-2 * ((n : ℝ) * Real.arcosh (Real.cos δ)⁻¹)) := by
  have hcos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [Real.pi_pos, hδ], hδπ⟩
  have hbase : 1 ≤ (Real.cos δ)⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hcos).2 (by simpa only [one_mul] using Real.cos_le_one δ)
  have hcosv : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc (abs_le.mp hhi)
  have hcosle : Real.cos v ≤ Real.cos δ := by
    rw [← Real.cos_abs v]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hδ
      (hhi.trans (by linarith only [Real.pi_pos])) hlo
  have habs : |Real.cos v / Real.cos δ| ≤ 1 := by
    rw [abs_div, abs_of_nonneg hcosv, abs_of_pos hcos]
    exact (div_le_one hcos).2 hcosle
  exact chebyshevResolvingKernel_le n habs hbase

end RiemannResearch.Analysis.MontgomeryFormFactor
