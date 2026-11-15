/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.LogFloorConvolution
import RiemannResearch.Analysis.LogProductPowerBounds
import RiemannResearch.Analysis.StretchedExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stretched logarithmic savings through reciprocal floor convolution

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 3.
The profile comparison retains the whole convolution. Shrinking the given
positive exponent to at most one half makes the compensating complete kernel
dominated by the convergent three-halves p-series.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.StretchedFloorConvolution
open LogFloorConvolution

def profile (x : ℝ) : ℝ := logProductPower (1 / 11) x

theorem profile_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ profile x := by
  exact Real.rpow_nonneg (mul_nonneg (by linarith : 0 ≤ x) (Real.log_nonneg hx)) _

theorem profile_le_self {x : ℝ} (hx : 6 ≤ x) : profile x ≤ x :=
  logProductPower_le_self (by norm_num) (by norm_num) hx

theorem profile_double_le {x : ℝ} (hx : 6 ≤ x) :
    profile (2 * x) ≤ 4 * profile x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlx := Real.log_nonneg hx1
  have hl2 : Real.log (2 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
    linarith
  have hbase : (2 * x) * Real.log (2 * x) ≤ 4 * (x * Real.log x) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * x)]
  unfold profile logProductPower
  calc
    ((2 * x) * Real.log (2 * x)) ^ (1 / 11 : ℝ) ≤
        (4 * (x * Real.log x)) ^ (1 / 11 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg (by positivity)
        (Real.log_nonneg (by linarith : 1 ≤ 2 * x))) hbase (by norm_num)
    _ = (4 : ℝ) ^ (1 / 11 : ℝ) * (x * Real.log x) ^ (1 / 11 : ℝ) :=
      Real.mul_rpow (by norm_num) (mul_nonneg hx0.le hlx)
    _ ≤ 4 * (x * Real.log x) ^ (1 / 11 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 4) (by norm_num))
        (Real.rpow_nonneg (mul_nonneg hx0.le hlx) _)

/-- A simple additive bound for the floor quotient logarithms. -/
theorem logWeight_floor_add (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    logWeight N ≤ logWeight (N / k) + logWeight k := by
  have hm : 0 < N / k := Nat.div_pos hkN hk
  have hN : 0 < N := hk.trans_le hkN
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmR : (1 : ℝ) ≤ (N / k : ℕ) := by exact_mod_cast hm
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk0 : (0 : ℝ) < k := by linarith
  have hm0 : (0 : ℝ) < (N / k : ℕ) := by linarith
  have hquot : N < k * (N / k + 1) := by
    have hmod := Nat.mod_lt N hk
    have heq := Nat.mod_add_div N k
    nlinarith
  have hquotR : (N : ℝ) ≤ 2 * (k : ℝ) * ((N / k : ℕ) : ℝ) := by
    have hh : (N : ℝ) < (k : ℝ) * (((N / k : ℕ) : ℝ) + 1) := by
      exact_mod_cast hquot
    nlinarith [mul_le_mul_of_nonneg_left
      (show (((N / k : ℕ) : ℝ) + 1) ≤ 2 * ((N / k : ℕ) : ℝ) by linarith) hk0.le]
  have hlog := Real.log_le_log hN0 hquotR
  rw [Real.log_mul (by positivity : 2 * (k : ℝ) ≠ 0) hm0.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hk0.ne'] at hlog
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  dsimp only [logWeight]
  linarith

/-- The exact floor indices need only a fixed factor-four profile loss. -/
theorem profile_floor_le (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    profile (logWeight N) ≤
      4 * (profile (logWeight (N / k)) + profile (logWeight k)) := by
  let M := max (logWeight (N / k)) (logWeight k)
  have hM : 6 ≤ M := (six_le_logWeight _).trans (le_max_left _ _)
  have hN : 1 ≤ logWeight N := by have h := six_le_logWeight N; linarith
  have hsum : logWeight N ≤ 2 * M := by
    have h := logWeight_floor_add N k hk hkN
    have hm := le_max_left (logWeight (N / k)) (logWeight k)
    have hk' := le_max_right (logWeight (N / k)) (logWeight k)
    dsimp only [M]
    linarith
  have hmon : profile (logWeight N) ≤ profile (2 * M) :=
    logProductPower_mono (1 / 11) (by norm_num) hN hsum
  have hmax : profile M ≤ profile (logWeight (N / k)) + profile (logWeight k) := by
    have hm := profile_nonneg (show 1 ≤ logWeight (N / k) by
      have h := six_le_logWeight (N / k); linarith)
    have hk' := profile_nonneg (show 1 ≤ logWeight k by
      have h := six_le_logWeight k; linarith)
    by_cases h : logWeight (N / k) ≤ logWeight k
    · dsimp only [M]
      rw [max_eq_right h]
      linarith
    · dsimp only [M]
      rw [max_eq_left (le_of_not_ge h)]
      linarith
  exact hmon.trans ((profile_double_le hM).trans (by linarith))

def kernel (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (a * profile (logWeight n)) / (n : ℝ) ^ 2

theorem kernel_nonneg (a : ℝ) (n : ℕ) : 0 ≤ kernel a n := by
  exact div_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- The compensating complete kernel is summable once the exponent is at most one half. -/
theorem summable_kernel {a : ℝ} (_ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    Summable (kernel a) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply (hs.mul_left (Real.exp 3)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 ≤ logWeight n := (logWeight_pos n).le
  have hp : 0 ≤ profile (logWeight n) := profile_nonneg (by
    have h := six_le_logWeight n; linarith)
  have hexponent : a * profile (logWeight n) ≤ (1 / 2 : ℝ) * logWeight n :=
    mul_le_mul ha2 (profile_le_self (six_le_logWeight n)) hp (by norm_num)
  have hexp : Real.exp ((1 / 2 : ℝ) * logWeight n) =
      Real.exp 3 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
    congr 1
    unfold logWeight
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg a n)]
  calc
    kernel a n ≤ Real.exp ((1 / 2 : ℝ) * logWeight n) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexponent) (sq_nonneg _)
    _ = Real.exp 3 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [hexp, show -(3 / 2 : ℝ) = (1 / 2 : ℝ) - 2 by ring,
        Real.rpow_sub hn0, Real.rpow_two]
      ring

def scale (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.exp (-a * profile (logWeight n))

theorem scale_nonneg (a : ℝ) (n : ℕ) : 0 ≤ scale a n := by
  exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le

theorem scale_pos (a : ℝ) {n : ℕ} (hn : 0 < n) : 0 < scale a n :=
  mul_pos (Nat.cast_pos.mpr hn) (Real.exp_pos _)

theorem scale_eventually_one_le {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ scale a n := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually_ge_atTop (Real.exp 6)] with n hn
  have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans_le hn
  have hl : 6 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 6) hn
    simpa only [Real.log_exp] using h
  have hp : 0 ≤ profile (logWeight n) := profile_nonneg (by
    have h := six_le_logWeight n; linarith)
  have hpa : a * profile (logWeight n) ≤ (1 / 2 : ℝ) * logWeight n :=
    mul_le_mul ha2 (profile_le_self (six_le_logWeight n)) hp (by norm_num)
  have hsign : 0 ≤ Real.log (n : ℝ) + -a * profile (logWeight n) := by
    dsimp only [logWeight] at hpa ⊢
    linarith
  calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (Real.log (n : ℝ) + -a * profile (logWeight n)) :=
      Real.exp_le_exp.mpr hsign
    _ = scale a n := by rw [Real.exp_add, Real.exp_log hn0]; rfl

/-- Absorb the provider's additive constant and all initial sites without
changing the stretched exponent. -/
theorem global_envelope_of_eventual (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (hzero : e 0 = 0) {a b C : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n : ℕ in atTop, e n ≤ b + C * scale a n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, e n ≤ D * scale a n := by
  have hev : ∀ᶠ n : ℕ in atTop, e n ≤ (b + C) * scale a n := by
    filter_upwards [hbound, scale_eventually_one_le ha ha2] with n hn hscale
    nlinarith [mul_le_mul_of_nonneg_left hscale hb]
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  let S : ℝ := ∑ n ∈ Finset.range M, e n / scale a n
  have hS : 0 ≤ S := Finset.sum_nonneg fun n _ =>
    div_nonneg (he n) (scale_nonneg _ _)
  refine ⟨b + C + S, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, hzero, scale]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  by_cases hnM : M ≤ n
  · exact (hM n hnM).trans
      (mul_le_mul_of_nonneg_right (by linarith : b + C ≤ b + C + S)
        (scale_nonneg _ _))
  · have hterm : e n / scale a n ≤ S := by
      change e n / scale a n ≤ ∑ i ∈ Finset.range M, e i / scale a i
      exact Finset.single_le_sum (f := fun i => e i / scale a i)
        (fun i _ => div_nonneg (he i) (scale_nonneg a i))
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hnM))
    have ht := (div_le_iff₀ (scale_pos a hn0)).mp hterm
    exact ht.trans (mul_le_mul_of_nonneg_right
      (by linarith : S ≤ b + C + S) (scale_nonneg _ _))

/-- Stretched decay transfers through the full floor convolution, with the
explicit exponent loss a↦a/4 and a convergent complete compensation kernel. -/
theorem floorConvolution_le (e : ℕ → ℝ) {a C : ℝ} (ha : 0 ≤ a)
    (ha2 : a ≤ 1 / 2) (hC : 0 ≤ C)
    (hbound : ∀ n, e n ≤ C * scale a n) (N : ℕ) :
    LogFloorConvolution.floorConvolution e N ≤
      (C * ∑' k, kernel a k) * scale (a / 4) N := by
  have hsum : (∑ k ∈ Finset.Icc 1 N, kernel a k) ≤ ∑' k, kernel a k :=
    (summable_kernel ha ha2).sum_le_tsum _ (fun k _ => kernel_nonneg a k)
  calc
    LogFloorConvolution.floorConvolution e N ≤
        ∑ k ∈ Finset.Icc 1 N, (C * scale (a / 4) N) * kernel a k := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
      have hprof := profile_floor_le N k hk0 hkN
      have hexp : Real.exp (-a * profile (logWeight (N / k))) ≤
          Real.exp (-(a / 4) * profile (logWeight N)) *
            Real.exp (a * profile (logWeight k)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hprof ha
        nlinarith
      have hmul : ((N / k : ℕ) : ℝ) * (k : ℝ) ≤ N := by
        exact_mod_cast (show (N / k) * k ≤ N by
          simpa only [Nat.mul_comm] using Nat.mul_div_le N k)
      calc
        e (N / k) / (k : ℝ) ≤ (C * scale a (N / k)) / (k : ℝ) :=
          div_le_div_of_nonneg_right (hbound _) hkR.le
        _ = (C * (((N / k : ℕ) : ℝ) * (k : ℝ)) / (k : ℝ) ^ 2) *
            Real.exp (-a * profile (logWeight (N / k))) := by
          unfold scale
          field_simp [hkR.ne'] <;> ring
        _ ≤ (C * (N : ℝ) / (k : ℝ) ^ 2) *
            Real.exp (-a * profile (logWeight (N / k))) := by gcongr
        _ ≤ (C * (N : ℝ) / (k : ℝ) ^ 2) *
            (Real.exp (-(a / 4) * profile (logWeight N)) *
              Real.exp (a * profile (logWeight k))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = (C * scale (a / 4) N) * kernel a k := by
          unfold scale kernel
          ring
    _ = (C * scale (a / 4) N) *
        (∑ k ∈ Finset.Icc 1 N, kernel a k) := by rw [Finset.mul_sum]
    _ ≤ (C * scale (a / 4) N) * (∑' k, kernel a k) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (scale_nonneg _ _))
    _ = _ := by ring

end RiemannResearch.Analysis.StretchedFloorConvolution
