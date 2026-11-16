/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.ActualZetaFourthMomentReduction

/-!
# Uniform mixed Ingham moment from the actual fourth moment

The proved mollifier second moment has one logarithm. Combining it with an
actual fourth-moment provider gives the sharp Hölder logarithmic exponent two,
uniformly for every integer cutoff between one and the height.
-/

noncomputable section
open MeasureTheory Complex Set
open scoped BigOperators

namespace RiemannResearch.Analysis.InghamMollifier

private theorem mixed_moment_power_factorization {C K T L : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hT : 0 < T) (hL : 0 < L) :
    (C * T * L ^ 4) ^ (1 / 3 : ℝ) * (K * T * L) ^ (2 / 3 : ℝ) =
      (C ^ (1 / 3 : ℝ) * K ^ (2 / 3 : ℝ)) * T * L ^ 2 := by
  rw [Real.mul_rpow (mul_nonneg hC hT.le) (pow_nonneg hL.le 4),
    Real.mul_rpow hC hT.le,
    Real.mul_rpow (mul_nonneg hK hT.le) hL.le,
    Real.mul_rpow hK hT.le, ← Real.rpow_natCast_mul hL.le]
  calc
    _ = (C ^ (1 / 3 : ℝ) * K ^ (2 / 3 : ℝ)) *
        (T ^ (1 / 3 : ℝ) * T ^ (2 / 3 : ℝ)) *
        (L ^ ((4 : ℝ) * (1 / 3 : ℝ)) * L ^ (2 / 3 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hT, ← Real.rpow_add hL]
      norm_num

/-- A uniform actual fourth-moment provider gives a uniform mixed moment of
order four thirds. The provider is an explicit premise of this transfer. -/
theorem exists_critical_error_moment_bound_of_fourth_moment
    (hfourth : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4) ≤
        C * T * (Real.log T) ^ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ X : ℕ,
      1 ≤ X → (X : ℝ) ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t) *
        mollifier X ((1 / 2 : ℂ) + I * t) - 1‖ ^ (4 / 3 : ℝ)) ≤
          C * T * (1 + Real.log T) ^ 2 := by
  obtain ⟨C₄, hC₄, hfourth⟩ := hfourth
  let K : ℝ := 12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨(2 : ℝ) ^ (1 / 3 : ℝ) *
    (C₄ ^ (1 / 3 : ℝ) * (2 * K) ^ (2 / 3 : ℝ) + 1), by positivity, ?_⟩
  intro T hT X hX hXT
  have hT0 : 0 < T := by linarith
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogXT := Real.log_le_log hX0 hXT
  let L : ℝ := 1 + Real.log T
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := by linarith
  have hfourth_base : C₄ * T * (Real.log T) ^ 4 ≤ C₄ * T * L ^ 4 := by
    apply mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlogT (by dsimp [L]; linarith) 4) (by positivity)
  have hsecond_base : K * (T + X) * (1 + Real.log X) ≤ (2 * K) * T * L := by
    calc
      _ ≤ K * (2 * T) * L := by
        apply mul_le_mul
          (mul_le_mul_of_nonneg_left (by linarith : T + X ≤ 2 * T) hK.le)
          (by dsimp [L]; linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hproduct :
      (C₄ * T * (Real.log T) ^ 4) ^ (1 / 3 : ℝ) *
          (K * (T + X) * (1 + Real.log X)) ^ (2 / 3 : ℝ) ≤
        (C₄ * T * L ^ 4) ^ (1 / 3 : ℝ) *
          ((2 * K) * T * L) ^ (2 / 3 : ℝ) := by
    apply mul_le_mul
      (Real.rpow_le_rpow (by positivity) hfourth_base (by norm_num))
      (Real.rpow_le_rpow (by positivity) hsecond_base (by norm_num))
      (by positivity) (by positivity)
  have hm := critical_error_moment_le_of_fourth_moment_bound hX
    (H := 0) (T := T) le_rfl hT0.le (hfourth T hT)
  simp only [sub_zero] at hm
  change (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t) *
    mollifier X ((1 / 2 : ℂ) + I * t) - 1‖ ^ (4 / 3 : ℝ)) ≤
    (2 : ℝ) ^ (1 / 3 : ℝ) *
      ((C₄ * T * (Real.log T) ^ 4) ^ (1 / 3 : ℝ) *
        (K * (T + X) * (1 + Real.log X)) ^ (2 / 3 : ℝ) + T) at hm
  have hTL : T ≤ T * L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  calc
    _ ≤ (2 : ℝ) ^ (1 / 3 : ℝ) *
      ((C₄ * T * (Real.log T) ^ 4) ^ (1 / 3 : ℝ) *
        (K * (T + X) * (1 + Real.log X)) ^ (2 / 3 : ℝ) + T) := hm
    _ ≤ (2 : ℝ) ^ (1 / 3 : ℝ) *
      ((C₄ * T * L ^ 4) ^ (1 / 3 : ℝ) * ((2 * K) * T * L) ^ (2 / 3 : ℝ) + T) :=
      mul_le_mul_of_nonneg_left (add_le_add hproduct le_rfl) (by positivity)
    _ = (2 : ℝ) ^ (1 / 3 : ℝ) *
      ((C₄ ^ (1 / 3 : ℝ) * (2 * K) ^ (2 / 3 : ℝ)) * T * L ^ 2 + T) := by
      rw [mixed_moment_power_factorization hC₄.le (by positivity) hT0 hL]
    _ ≤ (2 : ℝ) ^ (1 / 3 : ℝ) *
      ((C₄ ^ (1 / 3 : ℝ) * (2 * K) ^ (2 / 3 : ℝ)) * T * L ^ 2 + T * L ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hTL) (by positivity)
    _ = _ := by dsimp [L]; ring

/-- The same consequence in the conventional `T (log T)^2` form for `T ≥ 2`. -/
theorem exists_critical_error_moment_log_bound_of_fourth_moment
    (hfourth : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4) ≤
        C * T * (Real.log T) ^ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ X : ℕ,
      1 ≤ X → (X : ℝ) ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t) *
        mollifier X ((1 / 2 : ℂ) + I * t) - 1‖ ^ (4 / 3 : ℝ)) ≤
          C * T * (Real.log T) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_critical_error_moment_bound_of_fourth_moment hfourth
  refine ⟨9 * C, by positivity, ?_⟩
  intro T hT X hX hXT
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogT : (1 / 2 : ℝ) ≤ Real.log T :=
    hlog2.trans (Real.log_le_log (by norm_num) hT)
  have hlog : 1 + Real.log T ≤ 3 * Real.log T := by linarith
  calc
    _ ≤ C * T * (1 + Real.log T) ^ 2 := hb T hT X hX hXT
    _ ≤ C * T * (3 * Real.log T) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) hlog 2) (by positivity)
    _ = _ := by ring

end RiemannResearch.Analysis.InghamMollifier
