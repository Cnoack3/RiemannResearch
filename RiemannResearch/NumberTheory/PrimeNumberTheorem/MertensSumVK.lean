/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.VinogradovKorobovProfile
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Defs
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Bounds for the finite summatory Möbius function at real cutoffs

The source premise in the
second-order improvement is of the form of Lee and Leong, Theorem 1.1 (12),
https://arxiv.org/html/2208.06141v5.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.Analysis

/-- When the logarithmic growth of a profile leaves its weighted envelope
increasing, interpolation of a floor-constant function preserves the same
exponential rate and multiplicative constant on all large real cutoffs. -/
theorem floor_exponential_bound_eventually_iff
    (F φ : ℝ → ℝ) (a C : ℝ) (hC : 0 ≤ C)
    (hfloor : ∀ x : ℝ, F x = F (⌊x⌋₊ : ℝ))
    (hinc : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      a * (φ y - φ x) ≤ Real.log y - Real.log x) :
    (∀ᶠ N : ℕ in atTop, |F (N : ℝ)| ≤ C * (N : ℝ) * Real.exp (-a * φ (N : ℝ))) ↔
      (∀ᶠ x : ℝ in atTop, |F x| ≤ C * x * Real.exp (-a * φ x)) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  constructor
  · intro hNat
    have hf : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
    have hfloorCast : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)) atTop atTop := hcast.comp hf
    filter_upwards [hf.eventually hNat, hfloorCast.eventually hinc,
      hf.eventually (eventually_ge_atTop (1 : ℕ)), eventually_ge_atTop (1 : ℝ)] with x hN hφ hpos hx
    have hN0 : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
    have hx0 : 0 < x := by linarith
    have hlog := hφ x (Nat.floor_le hx0.le)
    have heq (z : ℝ) (hz : 0 < z) : z * Real.exp (-a * φ z) =
        Real.exp (Real.log z - a * φ z) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hz, neg_mul]
    have henv : (⌊x⌋₊ : ℝ) * Real.exp (-a * φ (⌊x⌋₊ : ℝ)) ≤
        x * Real.exp (-a * φ x) := by
      rw [heq _ hN0, heq _ hx0]
      exact Real.exp_le_exp.mpr (by linarith)
    calc
      |F x| = |F (⌊x⌋₊ : ℝ)| := congrArg abs (hfloor x)
      _ ≤ C * (⌊x⌋₊ : ℝ) * Real.exp (-a * φ (⌊x⌋₊ : ℝ)) := hN
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henv hC
  · intro hReal
    exact hcast.eventually hReal

/-- Walfisz's VK profile admits real and integer formulations with identical
constants. This compares cutoffs independently of an arithmetic proof. -/
theorem mertens_sum_vk_eventually_nat_iff_real (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C) :
    (∀ᶠ N : ℕ in atTop,
      |(M (N : ℝ))| ≤ C * (N : ℝ) * Real.exp (-a * vkProfile (N : ℝ))) ↔
      (∀ᶠ x : ℝ in atTop, |M x| ≤ C * x * Real.exp (-a * vkProfile x)) := by
  apply floor_exponential_bound_eventually_iff M vkProfile a C hC (fun x => by simp [M])
  filter_upwards [vkProfile_eventual_log_increment (1/a) (by positivity)] with x hx y hxy
  have h := mul_le_mul_of_nonneg_left (hx y hxy) ha.le
  rwa [← mul_assoc, show a * (1/a) = 1 by field_simp, one_mul] at h

/-- For the actual finite Möbius sum, the variable-coefficient estimate
retains the whole leading coefficient and each subcritical first correction. -/
theorem mertens_sum_vk_second_order (A r K k : ℝ)
    (hA : 0 < A) (hK : 0 < K) (hk : k < A * r / 5)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ K * x * Real.log x *
      Real.exp (-(A * (1 - r / Real.log (Real.log x)) ^ (-(1 / 5 : ℝ)) * vkProfile x))) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤ x *
      Real.exp (-A * vkProfile x - k * (vkProfile x / Real.log (Real.log x))) :=
  vk_second_order_of_variable_coefficient M A r K k hA hK hk hM

end RiemannResearch.NumberTheory.PrimeNumberTheorem
