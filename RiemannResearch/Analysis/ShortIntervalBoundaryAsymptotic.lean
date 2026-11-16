/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ShortIntervalBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp

/-! # Uniformly negligible prime-window boundary corrections

Source: the user-provided Montgomery_SC_Proof_Plan_2026-11-16.md, Section 5,
for the sub-square-root corollary. The proof uses the complete endpoint
correction and its unconditional bound in ShortIntervalBoundary.

The explicit bound is 32 H² log N / N when H² ≤ N and log N ≥ 1.
Consequently every moving schedule with H² log N / N → 0 is admissible.
The power-window corollary is uniform in all H ≤ N^(1/2-η), for each η > 0.
These are unconditional endpoint estimates, not signed prime-correlation
estimates or a proof of Montgomery signed cancellation.
-/

open Filter Finset
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ShortIntervalBoundaryAsymptotic
open ShortIntervalBoundary ShortIntervalVariance

theorem centered_boundary_normalized_le (N H : ℕ)
    (hN : (2 : ℝ) ≤ N) (hH : (2 : ℝ) ≤ H)
    (hlog : 1 ≤ Real.log N) (hsize : (H : ℝ) ^ 2 ≤ N) :
    |boundaryCorrection centeredMangoldt N H| /
      ((H : ℝ) * N * (Real.log N - Real.log H)) ≤
        32 * ((H : ℝ) ^ 2 * Real.log N / N) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) < H := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hHN : (H : ℝ) ≤ N := by nlinarith
  have hlogs : Real.log H ≤ Real.log N / 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (H : ℝ) ^ 2) hsize
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hD : 0 < Real.log N - Real.log H := by linarith
  have hbig : Real.log ((N : ℝ) + H + 2) + 1 ≤ 4 * Real.log N := by
    have hsq : 2 * (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hcube : 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) - 2 by linarith) (sq_nonneg (N : ℝ))]
    have hbase : (N : ℝ) + H + 2 ≤ (N : ℝ) ^ 3 := by nlinarith
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ)+H+2) hbase
    rw [Real.log_pow] at hl
    norm_num at hl
    linarith
  have hbig0 : 0 ≤ Real.log ((N : ℝ) + H + 2) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) + H + 2 by linarith)
    linarith
  have hB : |boundaryCorrection centeredMangoldt N H| ≤
      (32 / 3 : ℝ) * (H : ℝ) ^ 3 * (Real.log N) ^ 2 := by
    calc
      _ ≤ (2 / 3 : ℝ) * (H : ℝ) * ((H : ℝ)-1) * ((H : ℝ)-2) *
          (Real.log ((N : ℝ) + H + 2) + 1)^2 := centered_boundary_bound N H
      _ ≤ (2 / 3 : ℝ) * (H : ℝ) * H * H * (4 * Real.log N) ^ 2 := by
        gcongr <;> linarith
      _ = _ := by ring
  apply (div_le_iff₀ (mul_pos (mul_pos hH0 hN0) hD)).mpr
  have hEq : (32 * ((H : ℝ) ^ 2 * Real.log N / N)) *
      ((H : ℝ) * N * (Real.log N / 2)) =
        16 * (H : ℝ) ^ 3 * (Real.log N) ^ 2 := by
    field_simp
    <;> ring
  have hlow : 16 * (H : ℝ) ^ 3 * (Real.log N) ^ 2 ≤
      (32 * ((H : ℝ) ^ 2 * Real.log N / N)) *
        ((H : ℝ) * N * (Real.log N - Real.log H)) := by
    rw [← hEq]
    gcongr
    linarith
  calc
    _ ≤ (32 / 3 : ℝ) * (H : ℝ) ^ 3 * (Real.log N) ^ 2 := hB
    _ ≤ 16 * (H : ℝ) ^ 3 * (Real.log N) ^ 2 := by
      gcongr
      norm_num
    _ ≤ _ := hlow

theorem centered_boundary_power_bound (η : ℝ) (hη : 0 < η)
    (N H : ℕ) (hN : (2 : ℝ) ≤ N) (hH : (2 : ℝ) ≤ H)
    (hlog : 1 ≤ Real.log N)
    (hsize : (H : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - η)) :
    |boundaryCorrection centeredMangoldt N H| /
      ((H : ℝ) * N * (Real.log N - Real.log H)) ≤
        32 * (Real.log N / (N : ℝ) ^ (2 * η)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hs : (H : ℝ) ^ 2 ≤ (N : ℝ) ^ (1-2*η) := by
    calc
      _ ≤ ((N : ℝ) ^ ((1 : ℝ)/2-η))^2 := by gcongr
      _ = (N : ℝ) ^ (1-2*η) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 1
        push_cast
        ring
  have hsN : (H : ℝ) ^ 2 ≤ N := hs.trans (by
    calc
      (N : ℝ) ^ (1-2*η) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = N := Real.rpow_one _)
  calc
    _ ≤ 32 * ((H : ℝ) ^ 2 * Real.log N / N) :=
      centered_boundary_normalized_le N H hN hH hlog hsN
    _ ≤ 32 * ((N : ℝ) ^ (1-2*η) * Real.log N / N) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_sub hN0, Real.rpow_one]
      field_simp
      <;> ring

theorem boundary_power_rate_tendsto (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ => 32 * (Real.log N / (N : ℝ) ^ (2 * η)))
      atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_atTop (show 0 < 2*η by linarith)).tendsto_div_nhds_zero
  have hn := hh.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa using hn.const_mul 32

theorem centered_boundary_uniform (η : ℝ) (hη : 0 < η) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ H : ℕ,
      2 ≤ H → (H : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ)/2-η) →
      |boundaryCorrection centeredMangoldt N H| /
        ((H : ℝ) * N * (Real.log N - Real.log H)) < ε := by
  intro ε hε
  have hr := (boundary_power_rate_tendsto η hη).eventually (eventually_lt_nhds hε)
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hr, hl, eventually_ge_atTop 2] with N hr hl hN H hH hs
  exact (centered_boundary_power_bound η hη N H (by exact_mod_cast hN)
    (by exact_mod_cast hH) hl hs).trans_lt hr

/-- Any window schedule with H² log N / N → 0 has negligible boundary. -/
theorem centered_boundary_tendsto_of_scale (H : ℕ → ℕ)
    (hH : ∀ᶠ N : ℕ in atTop, 2 ≤ H N)
    (hscale : Tendsto (fun N : ℕ => (H N : ℝ) ^ 2 * Real.log N / N)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      |boundaryCorrection centeredMangoldt N (H N)| /
        ((H N : ℝ) * N * (Real.log N - Real.log (H N))))
      atTop (𝓝 0) := by
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 1)
  have hs := hscale.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hr : Tendsto (fun N : ℕ => 32 * ((H N : ℝ) ^ 2 * Real.log N / N))
      atTop (𝓝 0) := by simpa using hscale.const_mul 32
  have hconditions : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ≤ N ∧ (2 : ℝ) ≤ H N ∧ 1 ≤ Real.log N ∧ (H N : ℝ) ^ 2 ≤ N := by
    filter_upwards [hl, hs, hH, eventually_ge_atTop 2] with N hl hs hH hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hs' := (div_lt_iff₀ hN0).mp hs
    have hpow : (H N : ℝ) ^ 2 ≤ (H N : ℝ) ^ 2 * Real.log N := by
      nlinarith [sq_nonneg (H N : ℝ)]
    exact ⟨by exact_mod_cast hN, by exact_mod_cast hH, hl, by linarith⟩
  apply squeeze_zero' _ _ hr
  · filter_upwards [hconditions] with N hc
    have hHN0 : (0 : ℝ) < H N := lt_of_lt_of_le (by norm_num) hc.2.1
    have hlogs : Real.log (H N) ≤ Real.log N / 2 := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (H N : ℝ) ^ 2) hc.2.2.2
      rw [Real.log_pow] at h
      norm_num at h
      linarith
    apply div_nonneg (abs_nonneg _)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  · filter_upwards [hconditions] with N hc
    exact centered_boundary_normalized_le N (H N) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-- The user's logarithm-of-a-quotient normalization, with uniform quantifiers. -/
theorem centered_boundary_uniform_log_div (η : ℝ) (hη : 0 < η) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ H : ℕ,
      2 ≤ H → (H : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - η) →
      |boundaryCorrection centeredMangoldt N H| /
        ((N : ℝ) * H * Real.log ((N : ℝ) / H)) < ε := by
  intro ε hε
  filter_upwards [centered_boundary_uniform η hη ε hε, eventually_ge_atTop 2]
    with N hN hN2 H hH hs
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  simpa only [Real.log_div hN0 hH0, mul_comm (N : ℝ) (H : ℝ)] using hN H hH hs

end RiemannResearch.Analysis.ShortIntervalBoundaryAsymptotic
