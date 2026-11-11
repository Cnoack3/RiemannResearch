/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.EvenGapPrimeReduction
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp

/-! # Removing the corrected odd contribution uniformly

The elementary budget vanishes for every positive width H=o(N/log N).
In particular it vanishes in every fixed polynomial range H <= N^(1-epsilon).
The equivalence below retains all one-point and endpoint terms in evenResidual.
It does not prove that either side tends to zero.
-/

noncomputable section
open scoped Topology
open Filter
namespace RiemannResearch.Analysis.EvenGapPrimeAsymptotic
open ShortIntervalVariance EvenGapPrimeReduction

theorem normalized_budget_le (N H : ℕ) (hN : 2 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N) :
    (2 * (H : ℝ) ^ 2 * (Real.log ((N + H + 2 : ℕ) : ℝ)) ^ 2) /
        ((H : ℝ) * N * Real.log N) ≤ 18 * ((H : ℝ) * Real.log N / N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hh : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hhn : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hL0 : 0 ≤ Real.log ((N + H + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + H + 2 by omega))
  have hL : Real.log ((N + H + 2 : ℕ) : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    have hm : ((N + H + 2 : ℕ) : ℝ) ≤ (N : ℝ)^3 := by
      push_cast
      nlinarith [sq_nonneg ((N : ℝ) - 2), mul_nonneg hn.le (sq_nonneg ((N : ℝ) - 2))]
    have ht := Real.log_le_log (by positivity : (0 : ℝ) < ((N + H + 2 : ℕ) : ℝ)) hm
    simpa only [Real.log_pow, Nat.cast_ofNat] using ht
  have hs : (Real.log ((N + H + 2 : ℕ) : ℝ)) ^ 2 ≤ 9 * (Real.log (N : ℝ)) ^ 2 := by
    nlinarith
  calc
    _ = 2 * (H : ℝ) * (Real.log ((N + H + 2 : ℕ) : ℝ)) ^ 2 /
        ((N : ℝ) * Real.log N) := by field_simp
    _ ≤ 18 * (H : ℝ) * (Real.log (N : ℝ)) ^ 2 / ((N : ℝ) * Real.log N) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ = _ := by field_simp

theorem budget_tendsto_of_width (H : ℕ → ℕ)
    (hH : ∀ᶠ N in atTop, 1 ≤ H N ∧ H N ≤ N)
    (hwidth : Tendsto (fun N : ℕ => (H N : ℝ) * Real.log N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (2 * (H N : ℝ) ^ 2 * (Real.log ((N + H N + 2 : ℕ) : ℝ)) ^ 2) /
        ((H N : ℝ) * N * Real.log N)) atTop (𝓝 0) := by
  have hu := hwidth.const_mul 18
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [hH, eventually_ge_atTop 2] with N hh hn
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    positivity
  · filter_upwards [hH, eventually_ge_atTop 2] with N hh hn
    exact normalized_budget_le N (H N) hn hh.1 hh.2

/-- The corrected odd part is negligible in a range wider than every fixed polynomial range. -/
theorem evenResidual_iff_of_width (H : ℕ → ℕ)
    (hH : ∀ᶠ N in atTop, 1 ≤ H N ∧ H N ≤ N)
    (hwidth : Tendsto (fun N : ℕ => (H N : ℝ) * Real.log N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (centeredOffDiagonal N (H N) + (H N : ℝ) * N * Real.log (H N)) /
        ((H N : ℝ) * N * Real.log N)) atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ => evenResidual N (H N) /
      ((H N : ℝ) * N * Real.log N)) atTop (𝓝 0) := by
  apply evenResidual_tendsto_iff H (fun N => (H N : ℝ) * N * Real.log N)
  · filter_upwards [hH, eventually_ge_atTop 2] with N hh hn
    have hp : (0 : ℝ) < H N := by exact_mod_cast (show 0 < H N by omega)
    have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    positivity
  · exact budget_tendsto_of_width H hH hwidth

theorem polynomial_width_small (H : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hH : ∀ᶠ N in atTop, (H N : ℝ) ≤ (N : ℝ) ^ (1 - ε)) :
    Tendsto (fun N : ℕ => (H N : ℝ) * Real.log N / N) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)^ε) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_pow_atTop ε 1 hε).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop 2] with N hn
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    positivity
  · filter_upwards [hH, eventually_ge_atTop 2] with N hh hn
    have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    calc
      _ ≤ (N : ℝ) ^ (1 - ε) * Real.log N / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hl) hn0.le
      _ = _ := by rw [Real.rpow_sub hn0, Real.rpow_one]; field_simp

/-- No prime-distribution or zero hypothesis occurs in this polynomial-range reduction. -/
theorem evenResidual_iff_polynomial (H : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hH : ∀ᶠ N in atTop, 1 ≤ H N ∧ (H N : ℝ) ≤ (N : ℝ) ^ (1 - ε)) :
    Tendsto (fun N : ℕ =>
      (centeredOffDiagonal N (H N) + (H N : ℝ) * N * Real.log (H N)) /
        ((H N : ℝ) * N * Real.log N)) atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ => evenResidual N (H N) /
      ((H N : ℝ) * N * Real.log N)) atTop (𝓝 0) := by
  apply evenResidual_iff_of_width H
  · filter_upwards [hH, eventually_ge_atTop 1] with N hh hn
    refine ⟨hh.1, ?_⟩
    have hp : (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hn : (1 : ℝ) ≤ N) (show 1 - ε ≤ 1 by linarith)
    exact_mod_cast hh.2.trans hp
  · exact polynomial_width_small H ε hε (hH.mono (fun _ hh => hh.2))

end RiemannResearch.Analysis.EvenGapPrimeAsymptotic
