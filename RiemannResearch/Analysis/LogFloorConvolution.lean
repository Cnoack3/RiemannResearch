/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PolylogTailProfile
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Logarithmic envelopes through a reciprocal floor convolution

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 3.
This proof replaces the paper's square-root split by the exact elementary
comparison L(N) ≤ L(floor(N/k)) L(k), where L(n)=6+log n.
The full reciprocal-square logarithmic majorant is summable.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.LogFloorConvolution

def logWeight (n : ℕ) : ℝ := 6 + Real.log (n : ℝ)

theorem six_le_logWeight (n : ℕ) : 6 ≤ logWeight n := by
  by_cases hn : n = 0
  · simp [hn, logWeight]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact le_add_of_nonneg_right (Real.log_nonneg hn1)

theorem logWeight_pos (n : ℕ) : 0 < logWeight n := by
  have h := six_le_logWeight n
  linarith

def majorant (A n : ℕ) : ℝ := logWeight n ^ A / (n : ℝ) ^ 2

theorem majorant_nonneg (A n : ℕ) : 0 ≤ majorant A n :=
  div_nonneg (pow_nonneg (logWeight_pos n).le _) (sq_nonneg _)

private theorem power_le_double_power (A n : ℕ) :
    logWeight n ^ A ≤ logWeight n ^ (2 * A) := by
  have hbase : 1 ≤ logWeight n := by have h := six_le_logWeight n; linarith
  have hp : 1 ≤ logWeight n ^ A := one_le_pow₀ hbase
  rw [two_mul, pow_add]
  nlinarith

/-- The logarithmic reciprocal-square kernel has finite complete mass. -/
theorem summable_majorant (A : ℕ) : Summable (majorant A) := by
  let a : ℝ := Real.exp ((4 * A : ℕ) : ℝ)
  have ha : 1 ≤ a := by
    dsimp only [a]
    exact Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have hcond : ((4 * A : ℕ) : ℝ) ≤ 6 + Real.log a := by
    dsimp only [a]
    rw [Real.log_exp]
    linarith
  let C : ℝ := (6 + Real.log a) ^ (2 * A) / Real.sqrt a
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply (hs.mul_left C).of_norm_bounded_eventually_nat
  obtain ⟨M, hM⟩ := exists_nat_ge a
  filter_upwards [eventually_ge_atTop M] with n hn
  have hna : a ≤ (n : ℝ) := hM.trans (Nat.cast_le.mpr hn)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg A n)]
  calc
    majorant A n ≤ (6 + Real.log (n : ℝ)) ^ (2 * A) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (power_le_double_power A n) (sq_nonneg _)
    _ ≤ C * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
      PolylogTail.log_pow_div_sq_le A ha hna hcond

/-- Every fixed logarithmic power is eventually below the physical index. -/
theorem logWeight_power_eventually_le_index (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, logWeight n ^ A ≤ (n : ℝ) := by
  let a : ℝ := Real.exp ((4 * A : ℕ) : ℝ)
  have ha : 1 ≤ a := by
    dsimp only [a]
    exact Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have hcond : ((4 * A : ℕ) : ℝ) ≤ 6 + Real.log a := by
    dsimp only [a]
    rw [Real.log_exp]
    linarith
  let C : ℝ := (6 + Real.log a) ^ (2 * A) / Real.sqrt a
  have hC : 0 ≤ C := by
    have hl : 0 ≤ 6 + Real.log a := by linarith [Real.log_nonneg ha]
    exact div_nonneg (pow_nonneg hl _) (Real.sqrt_nonneg _)
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually_ge_atTop (max a ((C + 1) ^ 2))] with n hn
  have hna : a ≤ (n : ℝ) := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ (n : ℝ) := ha.trans hna
  have hCn : (C + 1) ^ 2 ≤ (n : ℝ) := (le_max_right _ _).trans hn
  have hsqrt : C ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt hCn
    rw [Real.sqrt_sq (by linarith : 0 ≤ C + 1)] at h
    linarith
  have hprof := PolylogTail.logProfile_sqrt_le A ha hna hcond
  have hmul : logWeight n ^ (2 * A) ≤ C * Real.sqrt (n : ℝ) :=
    (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < n))).mp hprof
  have hlast : C * Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (n : ℝ))
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (power_le_double_power A n).trans (hmul.trans hlast)

/-- Additive constants and finitely many initial sites can be absorbed into
one global logarithmic envelope, provided the zero coordinate is anchored. -/
theorem global_envelope_of_eventual (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (hzero : e 0 = 0) (A : ℕ) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n : ℕ in atTop,
      e n ≤ a + C * (n : ℝ) / logWeight n ^ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, e n ≤ D * (n : ℝ) / logWeight n ^ A := by
  have hev : ∀ᶠ n : ℕ in atTop,
      e n ≤ (a + C) * (n : ℝ) / logWeight n ^ A := by
    filter_upwards [hbound, logWeight_power_eventually_le_index A] with n hn hlog
    have hp : 0 < logWeight n ^ A := pow_pos (logWeight_pos n) _
    have hr : 1 ≤ (n : ℝ) / logWeight n ^ A :=
      (le_div_iff₀ hp).mpr (by simpa using hlog)
    have har := mul_le_mul_of_nonneg_left hr ha
    calc
      e n ≤ a + C * (n : ℝ) / logWeight n ^ A := hn
      _ ≤ (a + C) * (n : ℝ) / logWeight n ^ A := by
        rw [show (a + C) * (n : ℝ) / logWeight n ^ A =
          a * ((n : ℝ) / logWeight n ^ A) + C * (n : ℝ) / logWeight n ^ A by ring]
        linarith only [har]
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  let S : ℝ := ∑ n ∈ Finset.range M, e n * logWeight n ^ A / (n : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun n _ =>
    div_nonneg (mul_nonneg (he n) (pow_nonneg (logWeight_pos n).le _))
      (Nat.cast_nonneg _)
  refine ⟨a + C + S, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, hzero]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hp : 0 < logWeight n ^ A := pow_pos (logWeight_pos n) _
  by_cases hnM : M ≤ n
  · calc
      e n ≤ (a + C) * (n : ℝ) / logWeight n ^ A := hM n hnM
      _ ≤ (a + C + S) * (n : ℝ) / logWeight n ^ A := by
        apply div_le_div_of_nonneg_right _ hp.le
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS) (Nat.cast_nonneg n)
  · have hterm : e n * logWeight n ^ A / (n : ℝ) ≤ S := by
      change e n * logWeight n ^ A / (n : ℝ) ≤
        ∑ i ∈ Finset.range M, e i * logWeight i ^ A / (i : ℝ)
      exact Finset.single_le_sum (f := fun i => e i * logWeight i ^ A / (i : ℝ))
        (fun i _ => div_nonneg
          (mul_nonneg (he i) (pow_nonneg (logWeight_pos i).le A)) (Nat.cast_nonneg i))
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hnM))
    have hterm' := (div_le_iff₀ hn0).mp hterm
    apply (le_div_iff₀ hp).mpr
    have hcoeff : S ≤ a + C + S := by linarith
    exact hterm'.trans (mul_le_mul_of_nonneg_right hcoeff hn0.le)

/-- The floor quotient loses only a multiplicative logarithmic kernel. -/
theorem logWeight_floor_mul (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    logWeight N ≤ logWeight (N / k) * logWeight k := by
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
  have hlk := Real.log_nonneg hkR
  have hlm := Real.log_nonneg hmR
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  dsimp only [logWeight]
  nlinarith [mul_nonneg hlk hlm]

def floorConvolution (e : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, e (N / k) / (k : ℝ)

/-- A complete logarithmic envelope is stable under the reciprocal floor convolution. -/
theorem floorConvolution_le (e : ℕ → ℝ) (A : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, e n ≤ C * (n : ℝ) / logWeight n ^ A) (N : ℕ) :
    floorConvolution e N ≤
      (C * ∑' k, majorant A k) * (N : ℝ) / logWeight N ^ A := by
  have hmajorant := summable_majorant A
  have hsum : (∑ k ∈ Finset.Icc 1 N, majorant A k) ≤ ∑' k, majorant A k :=
    hmajorant.sum_le_tsum _ (fun k _ => majorant_nonneg A k)
  have hNpow : 0 < logWeight N ^ A := pow_pos (logWeight_pos N) _
  calc
    floorConvolution e N ≤
        ∑ k ∈ Finset.Icc 1 N,
          (C * (N : ℝ) / logWeight N ^ A) * majorant A k := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
      have hmpow : 0 < logWeight (N / k) ^ A :=
        pow_pos (logWeight_pos _) _
      have hpow : logWeight N ^ A ≤
          logWeight (N / k) ^ A * logWeight k ^ A := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (logWeight_pos N).le
          (logWeight_floor_mul N k hk0 hkN) A
      have hinv : 1 / logWeight (N / k) ^ A ≤
          logWeight k ^ A / logWeight N ^ A := by
        apply (div_le_div_iff₀ hmpow hNpow).mpr
        simpa only [one_mul, mul_comm] using hpow
      have hmul : ((N / k : ℕ) : ℝ) * (k : ℝ) ≤ N := by
        exact_mod_cast (show (N / k) * k ≤ N by
          simpa only [Nat.mul_comm] using Nat.mul_div_le N k)
      calc
        e (N / k) / (k : ℝ) ≤
            (C * ((N / k : ℕ) : ℝ) / logWeight (N / k) ^ A) / (k : ℝ) :=
          div_le_div_of_nonneg_right (hbound _) hkR.le
        _ = (C * (((N / k : ℕ) : ℝ) * (k : ℝ)) / (k : ℝ) ^ 2) *
            (1 / logWeight (N / k) ^ A) := by
          field_simp [hkR.ne', hmpow.ne'] <;> ring
        _ ≤ (C * (N : ℝ) / (k : ℝ) ^ 2) *
            (1 / logWeight (N / k) ^ A) := by
          gcongr
        _ ≤ (C * (N : ℝ) / (k : ℝ) ^ 2) *
            (logWeight k ^ A / logWeight N ^ A) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = (C * (N : ℝ) / logWeight N ^ A) * majorant A k := by
          unfold majorant
          ring
    _ = (C * (N : ℝ) / logWeight N ^ A) *
        (∑ k ∈ Finset.Icc 1 N, majorant A k) := by rw [Finset.mul_sum]
    _ ≤ (C * (N : ℝ) / logWeight N ^ A) * (∑' k, majorant A k) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end RiemannResearch.Analysis.LogFloorConvolution
