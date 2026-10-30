/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DiscreteGronwall
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Dyadic growth from vanishing multiplicative overhead

Source: the user-provided full-squarefree research handoff of 30 October 2026,
priority 4. The proof uses the existing DiscreteGronwall finite inequality and
Mathlib Cesaro convergence. It weakens the proposed harmonic overhead to any
nonnegative sequence tending to zero; it supplies no arithmetic RH budget.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.DyadicGronwall

/-- A nonnegative numerator that is o(n) is o(D n) whenever D has a positive
linear lower bound. -/
theorem div_tendsto_zero_of_linear_lower
    (f D : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ n, 0 ≤ f n)
    (hD : ∀ n, c * ((n + 1 : ℕ) : ℝ) ≤ D n)
    (hlim : Tendsto (fun n => f n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => f n / D n) atTop (𝓝 0) := by
  have hu : Tendsto
      (fun n => (f n / ((n + 1 : ℕ) : ℝ)) / c) atTop (𝓝 0) := by
    simpa using hlim.div_const c
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => by
      have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hd : 0 < D n := (mul_pos hc hn).trans_le (hD n)
      exact ha.trans_le (div_nonneg (hf n) hd.le))
  · intro b hb
    filter_upwards [hu.eventually (gt_mem_nhds hb)] with n hn
    have hnp : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hh := div_le_div_of_nonneg_left (hf n) (mul_pos hc hnp) (hD n)
    have heq : f n / (c * ((n + 1 : ℕ) : ℝ)) =
        (f n / ((n + 1 : ℕ) : ℝ)) / c := by ring
    rw [heq] at hh
    exact hh.trans_lt hn

/-- Cesàro convergence, with a successor denominator convenient for n=0. -/
theorem sum_div_succ_tendsto_zero (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hlim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => (∑ i ∈ Finset.range n, a i) /
      ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hces := (Asymptotics.isLittleO_sum_range_of_tendsto_zero hlim).tendsto_div_nhds_zero
  have hu : Tendsto
      (fun n => (∑ i ∈ Finset.range (n + 1), a i) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    hces.comp (tendsto_add_atTop_nat 1)
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => hb.trans_le
      (div_nonneg (Finset.sum_nonneg (fun i _ => ha i)) (by positivity)))
  · intro b hb
    filter_upwards [hu.eventually (gt_mem_nhds hb)] with n hn
    have hs : (∑ i ∈ Finset.range n, a i) ≤
        ∑ i ∈ Finset.range (n + 1), a i := by
      rw [Finset.sum_range_succ]
      linarith [ha n]
    exact (div_le_div_of_nonneg_right hs (by positivity)).trans_lt hn

/-- Constant additive forcing has a cumulative logarithm that is o(n). -/
theorem log_const_sum_div_succ_tendsto_zero (B : ℝ) (hB : 0 ≤ B) :
    Tendsto (fun n => Real.log (1 + ∑ _i ∈ Finset.range n, B) /
      ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto
      (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp hd
  have hc : Tendsto
      (fun n : ℕ => Real.log (B + 1) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := hd.const_div_atTop _
  have hu : Tendsto
      (fun n : ℕ => Real.log (B + 1) / ((n + 1 : ℕ) : ℝ) +
        Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by simpa only [add_zero] using hc.add hlog
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => by
      have hs : 0 ≤ ∑ _i ∈ Finset.range n, B :=
        Finset.sum_nonneg (fun _ _ => hB)
      exact hb.trans_le (div_nonneg (Real.log_nonneg (by linarith)) (by positivity)))
  · intro b hb
    filter_upwards [hu.eventually (gt_mem_nhds hb)] with n hn
    have hsum : (∑ _i ∈ Finset.range n, B) = (n : ℝ) * B := by simp
    have hp : 1 + (n : ℝ) * B ≤ (B + 1) * ((n + 1 : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith [show 0 ≤ (n : ℝ) by positivity]
    have hl := Real.log_le_log
      (show 0 < 1 + (n : ℝ) * B by positivity) hp
    rw [Real.log_mul (by positivity : B + 1 ≠ 0)
      (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)] at hl
    have hr := div_le_div_of_nonneg_right hl
      (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity)
    rw [add_div] at hr
    rw [hsum]
    exact hr.trans_lt hn

/-- Generic exponential-scale Gronwall consumer. Only vanishing multiplicative
overhead is needed; the coefficient need not have harmonic decay. -/
theorem relativeLog_tendsto_zero_of_vanishing_multiplier
    (E a L : ℕ → ℝ) (B c : ℝ)
    (hE : ∀ n, 0 ≤ E n) (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B) (hc : 0 < c)
    (hstep : ∀ n, E (n + 1) ≤ (1 + a n) * E n + B)
    (ha0 : Tendsto a atTop (𝓝 0))
    (hL : Tendsto L atTop atTop)
    (hlogL : ∀ n, c * ((n + 1 : ℕ) : ℝ) ≤ Real.log (L n)) :
    Tendsto (fun n => Real.log (1 + E n) / Real.log (L n))
      atTop (𝓝 0) := by
  apply DiscreteGronwall.relativeLog_tendsto_zero E a (fun _ => B) L
    hE ha (fun _ => hB) hstep hL
  · exact div_tendsto_zero_of_linear_lower
      (fun n => ∑ i ∈ Finset.range n, a i) (fun n => Real.log (L n)) c hc
      (fun n => Finset.sum_nonneg (fun i _ => ha i)) hlogL
      (sum_div_succ_tendsto_zero a ha ha0)
  · exact div_tendsto_zero_of_linear_lower
      (fun n => Real.log (1 + ∑ _i ∈ Finset.range n, B))
      (fun n => Real.log (L n)) c hc
      (fun n => Real.log_nonneg (by
        have hs := Finset.sum_nonneg (fun (_i : ℕ) (_ : _i ∈ Finset.range n) => hB)
        linarith)) hlogL (log_const_sum_div_succ_tendsto_zero B hB)

theorem log_dyadic_lower (m0 n : ℕ) :
    Real.log 2 * ((n + 1 : ℕ) : ℝ) ≤
      Real.log ((2 ^ (n + m0 + 1) + 2 : ℕ) : ℝ) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (n + m0 + 1) := by positivity
  have hb : (2 : ℝ) ^ (n + m0 + 1) ≤
      ((2 ^ (n + m0 + 1) + 2 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  have hl := Real.log_le_log hp hb
  rw [Real.log_pow] at hl
  have hn : ((n + 1 : ℕ) : ℝ) ≤ ((n + m0 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 ≤ n + m0 + 1 by omega)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem dyadic_tendsto_atTop (m0 : ℕ) :
    Tendsto (fun n : ℕ => 2 ^ (n + m0 + 1)) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa only [Function.comp_def, Nat.add_assoc] using hpow.comp (tendsto_add_atTop_nat (m0 + 1))

/-- Any eventual recurrence with vanishing nonnegative multiplicative overhead
and bounded additive forcing gives subpolynomial growth in physical dyadic heads.
This is a conditional analytic statement and supplies no arithmetic recurrence. -/
theorem relativeLog_dyadic_of_eventual_recurrence
    (E a : ℕ → ℝ) (B : ℝ) (m0 : ℕ)
    (hE : ∀ n, 0 ≤ E n) (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B)
    (ha0 : Tendsto a atTop (𝓝 0))
    (hstep : ∀ m, m0 ≤ m → E (2 ^ (m + 1)) ≤
      (1 + a m) * E (2 ^ m) + B) :
    Tendsto (fun n => Real.log (1 + E (2 ^ (n + m0 + 1))) /
      Real.log ((2 ^ (n + m0 + 1) + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ => n + m0 + 1) atTop atTop := by
    simpa only [Nat.add_assoc] using tendsto_add_atTop_nat (m0 + 1)
  apply relativeLog_tendsto_zero_of_vanishing_multiplier
    (fun n => E (2 ^ (n + m0 + 1))) (fun n => a (n + m0 + 1))
    (fun n => ((2 ^ (n + m0 + 1) + 2 : ℕ) : ℝ)) B (Real.log 2)
    (fun n => hE _) (fun n => ha _) hB (Real.log_pos (by norm_num))
  · intro n
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hstep (n + m0 + 1) (by omega)
  · exact ha0.comp hshift
  · exact tendsto_natCast_atTop_atTop.comp
      ((tendsto_add_atTop_nat 2).comp (dyadic_tendsto_atTop m0))
  · exact log_dyadic_lower m0

end RiemannResearch.Analysis.DyadicGronwall
