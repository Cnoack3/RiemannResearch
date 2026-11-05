/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuation of signed Möbius pairings

The uniform majorant and the vanishing near a point are explicit arithmetic
hypotheses. The latter follows for the damped Möbius family by squarefree
orthogonality where its series is absolutely convergent. See Bagchi (2006),
proof of Theorem 2 and Remark 4, https://arxiv.org/abs/math/0607733.
-/
noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis

/-- Continue a signed pairing of holomorphic scalar tests from an open
set of zeros to a point where every test takes the value one. -/
theorem mean_zero_of_holomorphic_pairing
    (U : Set ℂ) (z₀ z₁ : ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hz₀ : z₀ ∈ U) (hz₁ : z₁ ∈ U)
    (F : ℕ → ℂ → ℂ) (b : ℕ → ℂ) (G : ℕ → ℝ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hunit : ∀ n, F n z₁ = 1)
    (hdom : ∀ n z, z ∈ U → ‖F n z‖ ≤ G n)
    (hsum : Summable (fun n => ‖b n‖ * G n))
    (hann : (fun z => ∑' n, b n * F n z) =ᶠ[𝓝 z₀] 0) :
    ∑' n, b n = 0 := by
  have hf (n : ℕ) : DifferentiableOn ℂ (fun z => b n * F n z) U := by
    apply DifferentiableOn.mul _ (hF n)
    fun_prop
  have hd := Complex.differentiableOn_tsum_of_summable_norm hsum hf hU (fun n z hz => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hdom n z hz) (norm_nonneg _))
  have h := (hd.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconn hz₀ hann hz₁
  simpa only [hunit, mul_one, Pi.zero_apply] using h

/-- Boundary version for a normal family of damped Möbius tests. The tests
approach one termwise along x j and the signed pairing vanishes throughout U. -/
theorem mean_zero_of_holomorphic_pairing_at_boundary
    (U : Set ℂ) (z₀ : ℂ) (x : ℕ → ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hz₀ : z₀ ∈ U) (hx : ∀ j, x j ∈ U)
    (F : ℕ → ℂ → ℂ) (b : ℕ → ℂ) (G : ℕ → ℝ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hlim : ∀ n, Tendsto (fun j => F n (x j)) atTop (𝓝 1))
    (hdom : ∀ n z, z ∈ U → ‖F n z‖ ≤ G n)
    (hsum : Summable (fun n => ‖b n‖ * G n))
    (hann : (fun z => ∑' n, b n * F n z) =ᶠ[𝓝 z₀] 0) :
    ∑' n, b n = 0 := by
  have hd (n : ℕ) : DifferentiableOn ℂ (fun z => b n * F n z) U := by
    apply DifferentiableOn.mul _ (hF n)
    fun_prop
  have hbound (n : ℕ) (z : ℂ) (hz : z ∈ U) : ‖b n * F n z‖ ≤ ‖b n‖ * G n := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hdom n z hz) (norm_nonneg _)
  have hA := (Complex.differentiableOn_tsum_of_summable_norm hsum hd hU hbound).analyticOnNhd hU
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ hann
  have hterm (n : ℕ) : Tendsto (fun j => b n * F n (x j)) atTop (𝓝 (b n)) := by
    simpa only [mul_one] using (hlim n).const_mul (b n)
  have hT := tendsto_tsum_of_dominated_convergence hsum hterm
    (Eventually.of_forall (fun j n => hbound n (x j) (hx j)))
  have hzero : (fun j => ∑' n, b n * F n (x j)) =ᶠ[atTop] (fun _ => (0:ℂ)) :=
    Eventually.of_forall (fun j => hz (hx j))
  exact tendsto_nhds_unique (hT.congr' hzero) tendsto_const_nhds

/-- A pointwise growth exponent β for the witness gives the absolute moment
at every σ with σ+β<1 after multiplication by the physical n^(-2) weight. -/
theorem summable_mertens_shifted_power_moment (b : ℕ → ℂ) (σ β K C : ℝ)
    (hcrit : σ + β < 1) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ K * ((n : ℝ) + 1) ^ (β - 2)) :
    Summable (fun n : ℕ => ‖b n‖ * (C * ((n : ℝ) + 1) ^ σ)) := by
  have hs := Real.summable_nat_rpow.mpr (show β - 2 + σ < -1 by linarith)
  have ht : Summable (fun n : ℕ => ((n : ℝ)+1)^(β-2+σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (ht.mul_left (K*C))
  intro n
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc
    _ ≤ (K * ((n : ℝ)+1) ^ (β-2)) * (C * ((n : ℝ) + 1) ^ σ) :=
      mul_le_mul_of_nonneg_right (hb n) (mul_nonneg hC (Real.rpow_nonneg hx.le _))
    _ = _ := by rw [Real.rpow_add hx]; ring

/-- Given a uniform Perron bound of order σ for the damped tests,
the admissible exponent of the witness is 1−σ. -/
theorem mean_zero_of_power_bounded_holomorphic_pairing
    (U : Set ℂ) (z₀ z₁ : ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hz₀ : z₀ ∈ U) (hz₁ : z₁ ∈ U) (F : ℕ → ℂ → ℂ) (b : ℕ → ℂ)
    (σ β K C : ℝ) (hcrit : σ + β < 1) (hC : 0 ≤ C)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hunit : ∀ n, F n z₁ = 1)
    (hdom : ∀ (n : ℕ) z, z ∈ U → ‖F n z‖ ≤ C * ((n : ℝ) + 1) ^ σ)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ K * ((n : ℝ)+1)^(β-2))
    (hann : (fun z => ∑' n, b n * F n z) =ᶠ[𝓝 z₀] 0) :
    ∑' n, b n = 0 :=
  mean_zero_of_holomorphic_pairing U z₀ z₁ hU hconn hz₀ hz₁ F b _ hF hunit hdom
    (summable_mertens_shifted_power_moment b σ β K C hcrit hC hb) hann

end RiemannResearch.Analysis
