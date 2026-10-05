/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.FiniteHyperbolicHarmonicCap
import RiemannResearch.Analysis.LogMarginAsymptotics
import Mathlib.Tactic.FieldSimp

/-!
# Decay of the retained finite-height and logarithmic harmonic remainders

The actual Riemann--von Mangoldt lower bound, with the original full zero
count, kills the finite initial count and the log-square/logarithmic errors
in a density-window consumer. No analytic density or RH premise is used.
The error shape is motivated by Chourasiya--Simonic, arXiv:2507.15184v2,
Theorem 1 and the proof of Corollary 1:
https://arxiv.org/html/2507.15184v2.
No numerical source constant is asserted here.
-/

noncomputable section
open Filter
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Zeta23 FiniteHyperbolicHarmonicCap
theorem harmonic_log_remainder_bound (T : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hT : 0 < T) (hL : 1 ≤ Real.log T)
    (hdL : Real.log (d : ℝ) ≤ Real.log T/2)
    (hN : (1/(16*Real.pi))*T*Real.log T ≤ (Ncount 0 T : ℝ)) :
    harmonicHyperbolicCap d*(1+(Real.log T)^2)/(Ncount 0 T : ℝ) ≤
      16*Real.pi*((1+(Real.log T)^2)*(1+Real.log T))*Real.exp (-Real.log T/2) := by
  let L := Real.log T
  let P := (1+L^2)*(1+L)
  have hlog0 : 0 < Real.log T := by linarith
  have hL0 : 0 < L := hlog0
  have hN0 : (0 : ℝ) < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hds : (d : ℝ) ≤ Real.exp (L/2) := by
    rw [← Real.exp_log hd0]
    exact Real.exp_le_exp.mpr hdL
  have hW : harmonicHyperbolicCap d ≤ Real.exp (L/2)*(1+L) := by
    calc
      _ ≤ (d : ℝ)*(1+Real.log (d : ℝ)) := harmonicHyperbolicCap_le_card_log d hd
      _ ≤ (d : ℝ)*(1+L) := mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) hd0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hds (by positivity)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hexp : Real.exp (-L/2)*T = Real.exp (L/2) := by
    rw [show T = Real.exp L from (Real.exp_log hT).symm, ← Real.exp_add]
    congr 1
    ring
  have he :
      (16*Real.pi*P*Real.exp (-L/2))*((1/(16*Real.pi))*T*L) =
        Real.exp (L/2)*P*L := by
    rw [show (16*Real.pi*P*Real.exp (-L/2))*((1/(16*Real.pi))*T*L) =
      P*(Real.exp (-L/2)*T)*L by field_simp [Real.pi_pos.ne'], hexp]
    ring
  change harmonicHyperbolicCap d*(1+L^2)/(Ncount 0 T : ℝ) ≤
    16*Real.pi*P*Real.exp (-L/2)
  apply (div_le_iff₀ hN0).mpr
  calc
    _ ≤ Real.exp (L/2)*(1+L)*(1+L^2) :=
      mul_le_mul_of_nonneg_right hW (by positivity)
    _ = Real.exp (L/2)*P := by dsimp [P]; ring
    _ ≤ Real.exp (L/2)*P*L := by
      have h := mul_le_mul_of_nonneg_left hL
        (mul_nonneg (Real.exp_pos (L/2)).le hP)
      simpa [L] using h
    _ = _ := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)

/-- Any support at most sqrt(T) kills a fixed count and a log-square source
remainder. In particular this covers every square-root-log support schedule.
Only the existing unconditional actual count lower bound is used. -/
theorem harmonic_log_remainder_tendsto_zero (d : ℝ → ℕ)
    (hsupport : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ Real.log T/2) :
    Tendsto (fun T : ℝ =>
      harmonicHyperbolicCap (d T)*(1+(Real.log T)^2)/(Ncount 0 T : ℝ))
      atTop (nhds 0) := by
  have hm := (Real.cubic_mul_exp_neg_half_tendsto_zero.comp Real.tendsto_log_atTop).const_mul
    (16*Real.pi)
  have hm' : Tendsto (fun T : ℝ =>
      16*Real.pi*((1+(Real.log T)^2)*(1+Real.log T))*Real.exp (-Real.log T/2))
      atTop (nhds 0) := by
    convert hm using 1
    · funext T
      dsimp only [Function.comp_def]
      ring
    · norm_num
  refine squeeze_zero' ?_ ?_ hm'
  · exact Eventually.of_forall fun T => by
      exact div_nonneg (mul_nonneg (harmonicHyperbolicCap_nonneg _) (by positivity))
        (Nat.cast_nonneg _)
  · filter_upwards [hsupport, eventually_count_ge_log, eventually_gt_atTop (0:ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hs hn ht hl
    exact harmonic_log_remainder_bound T (d T) hs.1 ht hl hs.2 hn

/-- The retained initial count and both logarithmic remainders vanish
after the original normalization and multiplication by the harmonic cap. -/
theorem finiteHeight_log_remainder_tendsto_zero (d : ℝ → ℕ) (H B₂ B₃ : ℝ)
    (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hsupport : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ Real.log T/2) :
    Tendsto (fun T : ℝ =>
      (2*(B₂*(Real.log T)^2+B₃*Real.log T+(Ncount 0 H : ℝ))/
        (Ncount 0 T : ℝ))*harmonicHyperbolicCap (d T)) atTop (nhds 0) := by
  let C : ℝ := 2*(B₂+B₃+(Ncount 0 H : ℝ))
  have hm : Tendsto (fun T : ℝ =>
      C*(harmonicHyperbolicCap (d T)*(1+(Real.log T)^2)/(Ncount 0 T : ℝ)))
      atTop (nhds 0) := by
    simpa using (harmonic_log_remainder_tendsto_zero d hsupport).const_mul C
  refine squeeze_zero' ?_ ?_ hm
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
    have hl := Real.log_nonneg ht
    have hw := harmonicHyperbolicCap_nonneg (d T)
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
    have hl := Real.log_nonneg ht
    have hb : 2*(B₂*(Real.log T)^2+B₃*Real.log T+(Ncount 0 H : ℝ)) ≤
        C*(1+(Real.log T)^2) := by
      have h0 : Real.log T ≤ 1+(Real.log T)^2 := by nlinarith [sq_nonneg (Real.log T-1)]
      have h1 := mul_le_mul_of_nonneg_left h0 hB₃
      have h2 := mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (Real.log T)] : (1:ℝ) ≤ 1+(Real.log T)^2)
        (Nat.cast_nonneg (Ncount 0 H) : (0:ℝ) ≤ (Ncount 0 H : ℝ))
      dsimp [C]
      nlinarith
    calc
      _ ≤ (C*(1+(Real.log T)^2)/(Ncount 0 T : ℝ))*harmonicHyperbolicCap (d T) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hb (Nat.cast_nonneg _))
          (harmonicHyperbolicCap_nonneg _)
      _ = _ := by ring
end RiemannResearch.Analysis.ActualZeroOrdinate
