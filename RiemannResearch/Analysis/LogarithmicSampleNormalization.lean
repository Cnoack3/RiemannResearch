/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact count normalization and logarithmic remainder bounds

Source: the user's prime-torus Plancherel question (2026-10-28),
Mathlib finite-torus Fourier theory, and the cited project modules.
-/
noncomputable section
namespace RiemannResearch.Analysis
theorem count_normalization_ratio_bound
    (T N c : ℝ) (hT : 1 < T) (hc : 0 < c)
    (hN : c * T * Real.log T ≤ N) :
    0 < N ∧ T / N ≤ 1 / (c * Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  refine ⟨hN0, ?_⟩
  apply (div_le_div_iff₀ hN0 (mul_pos hc hL)).2
  nlinarith [hN]

theorem countNormalized_remainder_eq
    (T N : ℝ) (S A B : ℂ) (hT : T ≠ 0) (hN : N ≠ 0) :
    S / (N : ℂ) - A - ((T / N : ℝ) : ℂ) * B =
      ((T / N : ℝ) : ℂ) * ((S - (N : ℂ) * A) / (T : ℂ) - B) := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  have hNc : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN
  push_cast
  field_simp [hTc, hNc] <;> ring

theorem countNormalized_remainder_norm_le
    (T N c K M : ℝ) (S A B : ℂ)
    (hT : 1 < T) (hc : 0 < c) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hN : c * T * Real.log T ≤ N)
    (hE : ‖(S - (N : ℂ) * A) / (T : ℂ) - B‖ ≤ (K / Real.log T) * M) :
    ‖S / (N : ℂ) - A - ((T / N : ℝ) : ℂ) * B‖ ≤
      ((K / c) / (Real.log T) ^ 2) * M := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  obtain ⟨hN0, hratio⟩ := count_normalization_ratio_bound T N c hT hc hN
  rw [countNormalized_remainder_eq T N S A B hT0.ne' hN0.ne', norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hT0.le hN0.le)]
  calc
    _ ≤ (T / N) * ((K / Real.log T) * M) :=
      mul_le_mul_of_nonneg_left hE (div_nonneg hT0.le hN0.le)
    _ ≤ (1 / (c * Real.log T)) * ((K / Real.log T) * M) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by field_simp [hc.ne', hL.ne'] <;> ring

theorem countNormalized_error_norm_le
    (T N c K M : ℝ) (S A B : ℂ)
    (hT : 1 < T) (hL1 : 1 ≤ Real.log T) (hc : 0 < c)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hN : c * T * Real.log T ≤ N)
    (hB : ‖B‖ ≤ M)
    (hE : ‖(S - (N : ℂ) * A) / (T : ℂ) - B‖ ≤ (K / Real.log T) * M) :
    ‖S / (N : ℂ) - A‖ ≤ (((K + 1) / c) / Real.log T) * M := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  obtain ⟨hN0, hratio⟩ := count_normalization_ratio_bound T N c hT hc hN
  have hcorr := countNormalized_remainder_norm_le T N c K M S A B
    hT hc hK hM hN hE
  have hb : ‖((T / N : ℝ) : ℂ) * B‖ ≤ (1 / (c * Real.log T)) * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hT0.le hN0.le)]
    exact mul_le_mul hratio hB (norm_nonneg _) (by positivity)
  have hp : Real.log T ≤ (Real.log T) ^ 2 := by nlinarith
  have hk : (K / c) / (Real.log T) ^ 2 ≤ (K / c) / Real.log T := by
    apply (div_le_div_iff₀ (pow_pos hL 2) hL).2
    exact mul_le_mul_of_nonneg_left hp (div_nonneg hK hc.le)
  have he : S / (N : ℂ) - A =
      (S / (N : ℂ) - A - ((T / N : ℝ) : ℂ) * B) +
        ((T / N : ℝ) : ℂ) * B := by ring
  rw [he]
  calc
    _ ≤ ‖S / (N : ℂ) - A - ((T / N : ℝ) : ℂ) * B‖ +
        ‖((T / N : ℝ) : ℂ) * B‖ := norm_add_le _ _
    _ ≤ ((K / c) / (Real.log T) ^ 2) * M +
        (1 / (c * Real.log T)) * M := add_le_add hcorr hb
    _ ≤ ((K / c) / Real.log T) * M +
        (1 / (c * Real.log T)) * M :=
      add_le_add (mul_le_mul_of_nonneg_right hk hM) le_rfl
    _ = _ := by field_simp [hc.ne', hL.ne'] <;> ring
end RiemannResearch.Analysis
