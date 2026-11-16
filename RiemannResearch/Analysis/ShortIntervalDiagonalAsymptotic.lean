/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MangoldtSquareAsymptotic
import RiemannResearch.Analysis.ShortIntervalBoundary
import RiemannResearch.Analysis.OddGapPrimeAsymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! # Uniform actual prime-window diagonal asymptotics

Source: the user-provided Montgomery_SC_Proof_Plan_2026-11-16.md, Section 5,
for the diagonal target. MangoldtSquareAsymptotic supplies the actual
unconditional centered second moment. The finite shift identity here
retains every endpoint. Its nonnegative-square bound is H(H-1)M²/2.

For every fixed ε > 0, the diagonal error divided by
HN(log N-log H) tends uniformly to zero for 1 ≤ H ≤ N^(1-ε).
This supplies the diagonal part of the SC plan, not its signed
off-diagonal arithmetic estimate. No RH or prime-pair input is assumed.
-/

open Filter Finset
open scoped Topology BigOperators ArithmeticFunction
namespace RiemannResearch.Analysis.ShortIntervalDiagonalAsymptotic
open ShortIntervalBoundary ShortIntervalVariance MangoldtSquareAsymptotic
open OddGapPrimeAsymptotic

noncomputable def baseDiagonal (N : ℕ) : ℝ :=
  ∑ x ∈ range N, centeredMangoldt (x + 2)^2

theorem baseDiagonal_exact (N : ℕ) :
    baseDiagonal N = centeredSquareMass (N + 1) - 2 := by
  have hs := sum_range_add (fun n => (Λ n - 1)^2) 2 N
  have htwo : (∑ n ∈ range 2, (Λ n - 1)^2) = 2 := by norm_num [sum_range_succ]
  rw [htwo] at hs
  have hI : Iic (N + 1) = range (N + 2) := by
    ext n
    simp only [mem_Iic, mem_range]
    omega
  have heq : centeredSquareMass (N + 1) = 2 + baseDiagonal N := by
    simpa only [centeredSquareMass, hI, baseDiagonal,
      centeredMangoldt, Nat.add_comm 2 N, Nat.add_comm 2] using hs
  linarith

theorem log_shift_ratio_tendsto (a : ℕ) :
    Tendsto (fun N : ℕ => Real.log ((N + a : ℕ) : ℝ) / Real.log N)
      atTop (𝓝 1) := by
  have hr := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (nat_add_ratio_tendsto a)
  simp only [Real.log_one] at hr
  have hl : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (hr.div_atTop hl).add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hna : ((N + a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show N + a ≠ 0 by omega)
  have hlog : Real.log N ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  dsimp only [Function.comp_apply]
  rw [Real.log_div hna hn]
  field_simp
  <;> ring

theorem baseDiagonal_ratio_tendsto :
    Tendsto (fun N : ℕ => baseDiagonal N / ((N : ℝ) * Real.log N))
      atTop (𝓝 1) := by
  have hc := centeredSquareMass_ratio_tendsto.comp (nat_add_tendsto 1)
  have hh := (hc.mul (nat_add_ratio_tendsto 1)).mul (log_shift_ratio_tendsto 1)
  simp only [one_mul] at hh
  have hninv : Tendsto (fun N : ℕ => (2 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hninv.div_atTop hlog
  have hlim := hh.sub hsmall
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hna : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hl : Real.log N ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  have hla : Real.log ((N + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega)))
  dsimp only [Function.comp_apply]
  rw [baseDiagonal_exact]
  field_simp
  <;> ring

theorem centeredDiagonal_shift_exact (N H : ℕ) :
    centeredDiagonal N H = (H : ℝ) * baseDiagonal N +
      ∑ j ∈ range H, ∑ x ∈ range j,
        (centeredMangoldt (N + x + 2)^2 - centeredMangoldt (x + 2)^2) := by
  unfold centeredDiagonal baseDiagonal
  simp_rw [sum_shift_exact (fun x => centeredMangoldt (x + 2)^2) N]
  simp [sum_add_distrib]

theorem centeredDiagonal_shift_bound (N H : ℕ) :
    |centeredDiagonal N H - (H : ℝ) * baseDiagonal N| ≤
      (H : ℝ) * ((H : ℝ) - 1) / 2 * (Real.log ((N : ℝ) + H + 2) + 1)^2 := by
  rw [centeredDiagonal_shift_exact, add_sub_cancel_left]
  have hM : 0 ≤ Real.log ((N : ℝ) + H + 2) + 1 := by
    have := Real.log_nonneg (show 1 ≤ (N : ℝ) + H + 2 by
      have hN := Nat.cast_nonneg (α := ℝ) N
      have hH := Nat.cast_nonneg (α := ℝ) H
      linarith)
    linarith
  calc
    _ ≤ ∑ j ∈ range H, ∑ x ∈ range j,
        |centeredMangoldt (N + x + 2)^2 - centeredMangoldt (x + 2)^2| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j ∈ range H, ∑ _x ∈ range j, (Real.log ((N : ℝ) + H + 2) + 1)^2 := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro x hx
      have hjH := mem_range.mp hj
      have hxj := mem_range.mp hx
      have h1 := centeredMangoldt_abs_le (N+x+2) (N+H) (by omega) (by omega)
      have h2 := centeredMangoldt_abs_le (x+2) (N+H) (by omega) (by omega)
      simp only [Nat.cast_add] at h1 h2
      have hp1 : centeredMangoldt (N+x+2)^2 ≤ (Real.log ((N : ℝ)+H+2)+1)^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hp2 : centeredMangoldt (x+2)^2 ≤ (Real.log ((N : ℝ)+H+2)+1)^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h2 2
      exact abs_le.mpr ⟨by nlinarith [sq_nonneg (centeredMangoldt (N+x+2))],
        by nlinarith [sq_nonneg (centeredMangoldt (x+2))]⟩
    _ = _ := by
      simp only [sum_const, card_range, nsmul_eq_mul, ← sum_mul, range_linear_sum]

theorem centeredDiagonal_relative_bound (N H : ℕ)
    (hN : (2 : ℝ) ≤ N) (hH : (1 : ℝ) ≤ H)
    (hlog : 1 ≤ Real.log N) (hHN : (H : ℝ) ≤ N) :
    |centeredDiagonal N H - (H : ℝ) * N * Real.log N| /
      ((H : ℝ) * N * Real.log N) ≤
      |baseDiagonal N / ((N : ℝ) * Real.log N) - 1| +
        8 * ((H : ℝ) * Real.log N / N) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) < H := by linarith
  have hL0 : 0 < Real.log N := by linarith
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
    have := Real.log_nonneg (show 1 ≤ (N : ℝ) + H + 2 by linarith)
    linarith
  have hs : |centeredDiagonal N H - (H : ℝ) * baseDiagonal N| ≤
      8 * (H : ℝ) ^ 2 * (Real.log N)^2 := by
    calc
      _ ≤ (H : ℝ) * ((H : ℝ)-1) / 2 * (Real.log ((N : ℝ)+H+2)+1)^2 :=
        centeredDiagonal_shift_bound N H
      _ ≤ (H : ℝ) * H / 2 * (4 * Real.log N)^2 := by gcongr <;> linarith
      _ = _ := by ring
  have he : centeredDiagonal N H - (H : ℝ) * N * Real.log N =
      (centeredDiagonal N H - (H : ℝ) * baseDiagonal N) +
        (H : ℝ) * (baseDiagonal N - (N : ℝ)*Real.log N) := by ring
  have ha : |centeredDiagonal N H - (H : ℝ) * N * Real.log N| ≤
      8 * (H : ℝ) ^ 2 * (Real.log N)^2 +
        (H : ℝ) * |baseDiagonal N - (N : ℝ)*Real.log N| := by
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hH0]
    exact add_le_add hs le_rfl
  have hb : |baseDiagonal N / ((N : ℝ)*Real.log N) - 1| =
      |baseDiagonal N - (N : ℝ)*Real.log N| / ((N : ℝ)*Real.log N) := by
    have hid : baseDiagonal N / ((N : ℝ)*Real.log N) - 1 =
        (baseDiagonal N - (N : ℝ)*Real.log N) / ((N : ℝ)*Real.log N) := by
      field_simp
    rw [hid, abs_div, abs_of_pos (mul_pos hN0 hL0)]
  calc
    _ ≤ (8 * (H : ℝ) ^ 2 * (Real.log N)^2 +
        (H : ℝ)*|baseDiagonal N - (N : ℝ)*Real.log N|) /
        ((H : ℝ)*N*Real.log N) :=
      div_le_div_of_nonneg_right ha (by positivity)
    _ = _ := by rw [hb]; field_simp <;> ring

theorem centeredDiagonal_power_bound (ε : ℝ) (hε : 0 < ε)
    (N H : ℕ) (hN : (2 : ℝ) ≤ N) (hH : (1 : ℝ) ≤ H)
    (hlog : 1 ≤ Real.log N)
    (hsize : (H : ℝ) ≤ (N : ℝ) ^ (1 - ε)) :
    |centeredDiagonal N H - (H : ℝ)*N*Real.log N| /
      ((H : ℝ)*N*(Real.log N-Real.log H)) ≤
      (|baseDiagonal N / ((N : ℝ)*Real.log N) - 1| +
        8 * (Real.log N / (N : ℝ) ^ ε)) / ε := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) < H := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hHN : (H : ℝ) ≤ N := hsize.trans (by
    calc
      (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = N := Real.rpow_one _)
  have hlogs : Real.log H ≤ (1 - ε)*Real.log N := by
    have hl := Real.log_le_log hH0 hsize
    rwa [Real.log_rpow hN0] at hl
  have hD : 0 < Real.log N - Real.log H := by nlinarith
  have hrate : (H : ℝ)*Real.log N / N ≤ Real.log N / (N : ℝ) ^ ε := by
    calc
      _ ≤ (N : ℝ) ^ (1 - ε)*Real.log N / N := by gcongr
      _ = _ := by rw [Real.rpow_sub hN0, Real.rpow_one]; field_simp
  have hrel := (centeredDiagonal_relative_bound N H hN hH hlog hHN).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hrate (by norm_num : (0 : ℝ) ≤ 8)))
  have hnum := (div_le_iff₀ (mul_pos (mul_pos hH0 hN0) hL0)).mp hrel
  apply (div_le_iff₀ (mul_pos (mul_pos hH0 hN0) hD)).mpr
  have hnon : 0 ≤ |baseDiagonal N / ((N : ℝ)*Real.log N) - 1| +
      8 * (Real.log N / (N : ℝ) ^ ε) := by positivity
  calc
    _ ≤ (|baseDiagonal N / ((N : ℝ)*Real.log N) - 1| +
      8 * (Real.log N / (N : ℝ) ^ ε)) * ((H : ℝ)*N*Real.log N) := hnum
    _ = ((|baseDiagonal N / ((N : ℝ)*Real.log N) - 1| +
      8 * (Real.log N / (N : ℝ) ^ ε)) / ε) * ((H : ℝ)*N*(ε*Real.log N)) := by
        field_simp
    _ ≤ _ := by gcongr; nlinarith

/-- Uniform diagonal estimate in the full interior polynomial range. -/
theorem centeredDiagonal_uniform (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∀ H : ℕ,
      1 ≤ H → (H : ℝ) ≤ (N : ℝ) ^ (1 - ε) →
      |centeredDiagonal N H - (H : ℝ)*N*Real.log N| /
        ((H : ℝ)*N*(Real.log N-Real.log H)) < δ := by
  intro δ hδ
  have hb := (baseDiagonal_ratio_tendsto.sub_const 1).abs
  simp only [sub_self, abs_zero] at hb
  have hp := (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr := (hb.add (hp.const_mul 8)).div_const ε
  simp only [mul_zero, add_zero, zero_div] at hr
  have he := hr.eventually (eventually_lt_nhds hδ)
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 1)
  filter_upwards [he, hl, eventually_ge_atTop 2] with N he hl hN H hH hs
  exact (centeredDiagonal_power_bound ε hε N H (by exact_mod_cast hN)
    (by exact_mod_cast hH) hl hs).trans_lt he


end RiemannResearch.Analysis.ShortIntervalDiagonalAsymptotic
