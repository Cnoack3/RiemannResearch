/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHyperplaneCountermodel
import RiemannResearch.RH.QHeadResidualCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact complete and finite-support repairs in the matched hyperplane model

Source: the reciprocal-head investigation, 7 November 2026, Section 7.
The exact minimization identities retain the norm-square remainder, and the
complete minimum-norm family has the asserted positive norm-tail limit.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QHyperplaneCountermodel
open ZetaTwoHilbert
open QFiniteSupportDualCriterion

def residualTail (N : ℕ) : QHilbert := qOne - finiteHead N qOne

def headMean (N : ℕ) (x : QHilbert) : ℝ := inner ℝ qOne (finiteHead N x)

def tailRepair (N : ℕ) (x : QHilbert) : QHilbert :=
  finiteHead N x - (headMean N x / ‖residualTail N‖ ^ 2) • residualTail N

theorem qOne_coordinate_ne_zero (n : ℕ) : qOne n ≠ 0 := by
  intro hz
  have hp := congrFun qSequence_qOne (n + 1)
  rw [qSequence_succ, hz, zero_div] at hp
  simp [qOneSequence] at hp

theorem residualTail_ne_zero (N : ℕ) : residualTail N ≠ 0 := by
  intro hz
  have hn := congrArg (fun f : QHilbert => f N) hz
  change qOne N - finiteHead N qOne N = 0 at hn
  rw [finiteHead_apply_eq_zero N qOne N (le_refl N), sub_zero] at hn
  exact qOne_coordinate_ne_zero N hn

theorem residualTail_norm_sq_pos (N : ℕ) : 0 < ‖residualTail N‖ ^ 2 :=
  sq_pos_of_pos (norm_pos_iff.mpr (residualTail_ne_zero N))

theorem residualTail_mean (N : ℕ) :
    inner ℝ qOne (residualTail N) = ‖residualTail N‖ ^ 2 := by
  have ho := inner_finiteHead_tail N qOne qOne
  have he : qOne = finiteHead N qOne + residualTail N := by
    unfold residualTail
    abel
  calc
    _ = inner ℝ (finiteHead N qOne + residualTail N) (residualTail N) :=
      congrArg (fun z => inner ℝ z (residualTail N)) he
    _ = ‖residualTail N‖ ^ 2 := by
      rw [inner_add_left, show inner ℝ (finiteHead N qOne) (residualTail N) = 0 from ho,
        real_inner_self_eq_norm_sq, zero_add]

theorem tailRepair_mem (N : ℕ) (x : QHilbert) : tailRepair N x ∈ meanZero := by
  rw [mem_meanZero]
  unfold tailRepair
  rw [inner_sub_right, real_inner_smul_right, residualTail_mean]
  change headMean N x - (headMean N x / ‖residualTail N‖ ^ 2) * ‖residualTail N‖ ^ 2 = 0
  rw [div_mul_cancel₀ _ (ne_of_gt (residualTail_norm_sq_pos N))]
  ring

theorem tailRepair_head (N : ℕ) (x : QHilbert) (n : ℕ) (hn : n < N) :
    tailRepair N x n = x n := by
  change finiteHead N x n -
    (headMean N x / ‖residualTail N‖ ^ 2) * (qOne n - finiteHead N qOne n) = x n
  rw [finiteHead_apply_of_lt N x n hn, finiteHead_apply_of_lt N qOne n hn]
  ring

theorem tailRepair_energy (N : ℕ) (x : QHilbert) :
    ‖tailRepair N x‖ ^ 2 = ‖finiteHead N x‖ ^ 2 +
      (headMean N x) ^ 2 / ‖residualTail N‖ ^ 2 := by
  have hc := matching_head_residual_completion N x (tailRepair N x) qOne
    ((mem_meanZero _).mp (tailRepair_mem N x)) (tailRepair_head N x)
    (ne_of_gt (residualTail_norm_sq_pos N))
  dsimp only at hc
  have hr : tailRepair N x - finiteHead N x +
      (headMean N x / ‖residualTail N‖ ^ 2) • residualTail N = 0 := by
    unfold tailRepair
    abel
  change ‖tailRepair N x‖ ^ 2 = ‖finiteHead N x‖ ^ 2 +
      (headMean N x) ^ 2 / ‖residualTail N‖ ^ 2 +
      ‖tailRepair N x - finiteHead N x +
        (headMean N x / ‖residualTail N‖ ^ 2) • residualTail N‖ ^ 2 at hc
  simpa only [hr, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using hc

/-- Complete exact minimization, including the unique-minimizer remainder. -/
theorem tailRepair_completion (N : ℕ) (x F : QHilbert)
    (hF : F ∈ meanZero) (hh : ∀ n < N, F n = x n) :
    ‖F‖ ^ 2 = ‖tailRepair N x‖ ^ 2 + ‖F - tailRepair N x‖ ^ 2 := by
  have hc := matching_head_residual_completion N x F qOne
    ((mem_meanZero _).mp hF) hh (ne_of_gt (residualTail_norm_sq_pos N))
  dsimp only at hc
  have hr : F - finiteHead N x +
      (headMean N x / ‖residualTail N‖ ^ 2) • residualTail N = F - tailRepair N x := by
    unfold tailRepair
    abel
  change ‖F‖ ^ 2 = ‖finiteHead N x‖ ^ 2 +
      (headMean N x) ^ 2 / ‖residualTail N‖ ^ 2 +
      ‖F - finiteHead N x +
        (headMean N x / ‖residualTail N‖ ^ 2) • residualTail N‖ ^ 2 at hc
  rw [hr, ← tailRepair_energy] at hc
  exact hc

theorem tailRepair_unique (N : ℕ) (x F : QHilbert)
    (hF : F ∈ meanZero) (hh : ∀ n < N, F n = x n)
    (hn : ‖F‖ = ‖tailRepair N x‖) : F = tailRepair N x := by
  have hc := tailRepair_completion N x F hF hh
  rw [hn] at hc
  have hz : ‖F - tailRepair N x‖ = 0 := by nlinarith [norm_nonneg (F - tailRepair N x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem residualTail_tendsto : Tendsto residualTail atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => qOne - finiteHead N qOne) atTop (𝓝 0)
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => qOne) atTop (𝓝 qOne)).sub
    (finiteHead_tendsto qOne)
  simpa only [residualTail, sub_self] using h

theorem headMean_tendsto (x : QHilbert) :
    Tendsto (fun N => headMean N x) atTop (𝓝 (inner ℝ qOne x)) := by
  have h : Tendsto (fun N => inner ℝ qOne (finiteHead N x)) atTop
      (𝓝 (inner ℝ qOne x)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => qOne) atTop (𝓝 qOne)).inner
      (finiteHead_tendsto x)
  exact h

theorem tailRepair_product_sq (N : ℕ) (x : QHilbert) :
    (‖tailRepair N x‖ * ‖residualTail N‖) ^ 2 =
      ‖finiteHead N x‖ ^ 2 * ‖residualTail N‖ ^ 2 + (headMean N x) ^ 2 := by
  rw [mul_pow, tailRepair_energy, add_mul,
    div_mul_cancel₀ _ (ne_of_gt (residualTail_norm_sq_pos N))]

theorem tailRepair_product_tendsto (x : QHilbert) :
    Tendsto (fun N => ‖tailRepair N x‖ * ‖residualTail N‖) atTop
      (𝓝 |inner ℝ qOne x|) := by
  have ht : Tendsto (fun N => ‖residualTail N‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using residualTail_tendsto.norm
  have hs := (((finiteHead_tendsto x).norm.pow 2).mul (ht.pow 2)).add
    ((headMean_tendsto x).pow 2)
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at hs
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have he (N : ℕ) :
      Real.sqrt (‖finiteHead N x‖ ^ 2 * ‖residualTail N‖ ^ 2 + (headMean N x) ^ 2) =
        ‖tailRepair N x‖ * ‖residualTail N‖ := by
    rw [← tailRepair_product_sq, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa only [Function.comp_def, he, Real.sqrt_sq_eq_abs] using hsqrt

/-- Exact-head repairs exist and minimize energy, yet their residual-tail
product converges to a positive number for the explicit matched reciprocal d. -/
theorem countermodel_positive_product_limit :
    Tendsto (fun N => ‖tailRepair N reciprocalTarget‖ * ‖residualTail N‖) atTop
      (𝓝 (inner ℝ qOne reciprocalTarget)) := by
  simpa only [abs_of_pos target_mean_pos] using tailRepair_product_tendsto reciprocalTarget

end RiemannResearch.RH.QHyperplaneCountermodel
