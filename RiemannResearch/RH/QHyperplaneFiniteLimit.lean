/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHyperplaneTailMass
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Positive obstruction for finite repairs along M=N²

Source: the reciprocal-head investigation, 7 November 2026, Section 7.
The denominator ratio is the proved actual Q block-mass ratio, and every
finite repair is legal, agrees with its prescribed head, and has finite support.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QHyperplaneCountermodel
open ZetaTwoHilbert QFiniteSupportDualCriterion

theorem blockRepair_product_sq (N M : ℕ) (hNM : N < M) (x : QHilbert) :
    (‖blockRepair N M x‖ * ‖residualTail N‖) ^ 2 =
      ‖finiteHead N x‖ ^ 2 * ‖residualTail N‖ ^ 2 +
        (headMean N x) ^ 2 * (‖residualTail N‖ ^ 2 / ‖blockTail N M‖ ^ 2) := by
  rw [mul_pow, blockRepair_energy N M hNM x]
  ring

/-- The explicit finite-support schedule M=N² has the same sharp positive
limit as the complete minimum-norm correction. -/
theorem quadratic_blockRepair_product_tendsto (x : QHilbert) :
    Tendsto (fun N : ℕ => ‖blockRepair N (N ^ 2) x‖ * ‖residualTail N‖)
      atTop (𝓝 |inner ℝ qOne x|) := by
  have ht : Tendsto (fun N => ‖residualTail N‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using residualTail_tendsto.norm.pow 2
  have hinv : Tendsto
      (fun N : ℕ => ‖residualTail N‖ ^ 2 / ‖blockTail N (N ^ 2)‖ ^ 2) atTop (𝓝 1) := by
    have h := quadratic_block_mass_ratio_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [inv_div, inv_one] using h
  have hs := (((finiteHead_tendsto x).norm.pow 2).mul ht).add
    (((headMean_tendsto x).pow 2).mul hinv)
  simp only [mul_zero, mul_one, zero_add] at hs
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have he :
      (fun N : ℕ => Real.sqrt (‖finiteHead N x‖ ^ 2 * ‖residualTail N‖ ^ 2 +
        (headMean N x) ^ 2 * (‖residualTail N‖ ^ 2 / ‖blockTail N (N ^ 2)‖ ^ 2)))
        =ᶠ[atTop] (fun N => ‖blockRepair N (N ^ 2) x‖ * ‖residualTail N‖) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNM : N < N ^ 2 := by nlinarith
    rw [← blockRepair_product_sq N (N ^ 2) hNM x,
      Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have h := hsqrt.congr' he
  simpa only [Real.sqrt_sq_eq_abs] using h

theorem quadratic_countermodel_positive_product_limit :
    Tendsto (fun N : ℕ => ‖blockRepair N (N ^ 2) reciprocalTarget‖ * ‖residualTail N‖)
      atTop (𝓝 (inner ℝ qOne reciprocalTarget)) := by
  simpa only [abs_of_pos target_mean_pos] using quadratic_blockRepair_product_tendsto reciprocalTarget

/-- This combines the computed finite minimizers, their actual support, and
the positive matched-target limit in one certificate. -/
theorem finite_countermodel_certificate :
    (∀ N : ℕ, 2 ≤ N → blockRepair N (N ^ 2) reciprocalTarget ∈ meanZero ∧
      (∀ n < N, blockRepair N (N ^ 2) reciprocalTarget n = reciprocalTarget n) ∧
      (∀ n, N ^ 2 ≤ n → blockRepair N (N ^ 2) reciprocalTarget n = 0)) ∧
    0 < inner ℝ qOne reciprocalTarget ∧
    Tendsto (fun N : ℕ => ‖blockRepair N (N ^ 2) reciprocalTarget‖ * ‖residualTail N‖)
      atTop (𝓝 (inner ℝ qOne reciprocalTarget)) := by
  refine ⟨?_, target_mean_pos, quadratic_countermodel_positive_product_limit⟩
  intro N hN
  have hNM : N < N ^ 2 := by nlinarith
  exact ⟨blockRepair_mem N (N ^ 2) hNM reciprocalTarget,
    blockRepair_head N (N ^ 2) hNM.le reciprocalTarget,
    blockRepair_supported N (N ^ 2) hNM.le reciprocalTarget⟩

end RiemannResearch.RH.QHyperplaneCountermodel
