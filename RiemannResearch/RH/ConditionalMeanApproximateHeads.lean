/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalMeanHeadMinimum
import RiemannResearch.RH.ConditionalMeanHeadObstruction
import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.RH.WeilExplicitFormula.ZetaReflect

/-!
# Approximate heads, sparse energy bounds, and zeta zero locations

Source: user-requested continuation of the RH program. The proofs extend the
signed Mellin obstruction in ConditionalMeanHeadObstruction with the weighted
head-tail inequality in Analysis.WeightedComplexPairing.

Exact interpolation is replaced by convergence of the weighted head error.
A polynomial energy bound is required only at arbitrarily large good indices.
Subpolynomial bounds imply actual mathlib RH; a fixed exponent alpha confines
all nontrivial zeros to [(1-alpha)/2, (1+alpha)/2].

These are conditional research reductions: no arithmetic witness family with
the requisite bounds is constructed.
-/
noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative
set_option backward.isDefEq.respectTransparency false

/-- Weighted error of the actual Cesaro conditional mean on the first N positive endpoints. -/
def conditionalHeadError (N : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, conditionalWeight k * (1 - cesaro g (k + 1)) ^ 2

theorem conditionalHeadError_nonneg (N : ℕ) (g : ℕ → ℝ) :
    0 ≤ conditionalHeadError N g :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))

/-- Exact signed Mellin annihilation yields a head-error/tail-energy tradeoff. -/
theorem approximate_head_dual_obstruction
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (N : ℕ) {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A) :
    ‖partialSum (mellinSecond s) N‖ ^ 2 ≤
      2 * conditionalMellinDualSquare s * conditionalHeadError N g +
      2 * dualTail s N * conditionalMeanSquare g := by
  have henergy : Summable (fun k => conditionalWeight k * ‖(cesaro g (k + 1) : ℂ)‖ ^ 2) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      legal_conditionalMeanSquare_summable A hA hg
  have hzero : (∑' k : ℕ, mellinSecond s (k + 1) * (cesaro g (k + 1) : ℂ)) = 0 := by
    simpa only [mean_ofReal] using legal_second_pairing_zero A hA s hs hs1 hz hg
  have h := Analysis.WeightedPairing.prefix_obstruction_of_pairing_zero
    conditionalWeight conditionalWeight_pos (fun k => mellinSecond s (k + 1))
    (fun k => (cesaro g (k + 1) : ℂ)) (mellinSecond_dual_summable s hs) henergy hzero N
  simpa only [partialSum, conditionalHeadError, conditionalMellinDualSquare,
    conditionalMeanSquare, dualTail, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- The tail has the explicit decay exponent 1 - 2 Re(s), uniformly in legal witnesses. -/
theorem approximate_head_scaled_obstruction_eventually
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ legalSeedSpan A,
      (1 / 4 : ℝ) ≤
        2 * conditionalMellinDualSquare s * conditionalHeadError N g +
        2 * (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
          (N : ℝ) ^ (1 - 2 * s.re) * conditionalMeanSquare g := by
  filter_upwards [mellinSecond_prefix_eventually s hs, eventually_ge_atTop 1] with N hp hN
  intro g hg
  have hob := hp.trans (approximate_head_dual_obstruction A hA s hs hs1 hz N hg)
  have ht := mul_le_mul_of_nonneg_right (dualTail_le s hs N hN)
    (conditionalMeanSquare_nonneg g)
  nlinarith

/-- Approximate heads with an energy exponent below a zero's gap rule out that zero.
Only arbitrarily large good indices are needed for the energy bound. -/
theorem zeta_ne_zero_of_sparse_polynomial_approximate_heads
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hY : Tendsto Y atTop atTop)
    (hhead : Tendsto (fun j => conditionalHeadError (Y j) (g j)) atTop (𝓝 0))
    (α C : ℝ)
    (hbound : ∃ᶠ j in atTop, conditionalMeanSquare (g j) ≤ C * (Y j : ℝ) ^ α)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hα : α < 2 * s.re - 1) : riemannZeta s ≠ 0 := by
  intro hz
  let ε : ℝ := 2 * s.re - 1 - α
  have hε : 0 < ε := by dsimp [ε]; linarith
  let K : ℝ := 3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hd.le
  have hyR : Tendsto (fun j => (Y j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hY
  have hdecay := ((tendsto_rpow_neg_atTop hε).comp hyR).const_mul (2 * K * C)
  have hheadlim := hhead.const_mul (2 * conditionalMellinDualSquare s)
  have hsmall : ∀ᶠ j in atTop,
      2 * conditionalMellinDualSquare s * conditionalHeadError (Y j) (g j) +
      (2 * K * C) * (Y j : ℝ) ^ (-ε) < 1 / 4 := by
    have hh : Tendsto (fun j =>
        2 * conditionalMellinDualSquare s * conditionalHeadError (Y j) (g j) +
        (2 * K * C) * (Y j : ℝ) ^ (-ε)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero, add_zero] using hheadlim.add hdecay
    exact hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hob := hY.eventually (approximate_head_scaled_obstruction_eventually A hA s hs hs1 hz)
  have hpos := hY.eventually (eventually_ge_atTop 1)
  obtain ⟨j, hjbound, hj, hjpos, hjsmall⟩ :=
    (hbound.and_eventually (hob.and (hpos.and hsmall))).exists
  have hypos : (0 : ℝ) < Y j := by exact_mod_cast hjpos
  have hbase := hj (g j) (hg j)
  change (1 / 4 : ℝ) ≤
    2 * conditionalMellinDualSquare s * conditionalHeadError (Y j) (g j) +
      2 * K * (Y j : ℝ) ^ (1 - 2 * s.re) * conditionalMeanSquare (g j) at hbase
  have hupper := mul_le_mul_of_nonneg_left hjbound
    (show 0 ≤ 2 * K * (Y j : ℝ) ^ (1 - 2 * s.re) by positivity)
  have heq : (2 * K * (Y j : ℝ) ^ (1 - 2 * s.re)) *
      (C * (Y j : ℝ) ^ α) = (2 * K * C) * (Y j : ℝ) ^ (-ε) := by
    calc
      _ = (2 * K * C) * ((Y j : ℝ) ^ (1 - 2 * s.re) * (Y j : ℝ) ^ α) := by ring
      _ = _ := by
        rw [← Real.rpow_add hypos]
        congr 2
        dsimp [ε]
        ring
  rw [heq] at hupper
  linarith

theorem conditionalHeadError_eq_zero_of_exact_head
    (N : ℕ) {g : ℕ → ℝ}
    (hhead : ∀ n, 0 < n → n ≤ N → g n = 1) :
    conditionalHeadError N g = 0 := by
  unfold conditionalHeadError
  apply Finset.sum_eq_zero
  intro k hk
  rw [cesaro_eq_one_of_exact_head N hhead (k + 1) (Nat.succ_pos k)
    (Nat.succ_le_of_lt (Finset.mem_range.mp hk))]
  simp

/-- The good indices and constants may depend on the positive exponent. -/
def SparseSubpolynomialConditionalMean (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
    ∃ᶠ j : ℕ in atTop, conditionalMeanSquare (g j) ≤ C * (Y j : ℝ) ^ ε

/-- Conditional research reduction: the legal family and its two analytic bounds
remain hypotheses. No exact head interpolation or full-error convergence is assumed. -/
theorem riemannHypothesis_of_sparse_subpolynomial_approximate_heads
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hY : Tendsto Y atTop atTop)
    (hhead : Tendsto (fun j => conditionalHeadError (Y j) (g j)) atTop (𝓝 0))
    (hsub : SparseSubpolynomialConditionalMean g Y) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hright (s : ℂ) (hsz : riemannZeta s = 0)
      (hslt : s.re < 1) : s.re ≤ 1 / 2 := by
    by_contra h
    have hs : 1 / 2 < s.re := lt_of_not_ge h
    have hsne : s ≠ 1 := by intro he; simp [he] at hslt
    obtain ⟨C, hbound⟩ := hsub (s.re - 1 / 2) (by linarith)
    exact zeta_ne_zero_of_sparse_polynomial_approximate_heads
      A hA g Y hg hY hhead (s.re - 1 / 2) C hbound s hs hsne (by linarith) hsz
  have href := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hr := hright (Zeta23.reflect ρ) href.1 href.2.2
  have hl := hright ρ hz h1
  simp [Zeta23.reflect] at hr
  linarith

/-- Polynomial energy growth confines all nontrivial zeros to a symmetric strip. -/
theorem nontrivial_zero_strip_of_sparse_polynomial_approximate_heads
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hY : Tendsto Y atTop atTop)
    (hhead : Tendsto (fun j => conditionalHeadError (Y j) (g j)) atTop (𝓝 0))
    (α : ℝ) (hα : 0 ≤ α) (C : ℝ)
    (hbound : ∃ᶠ j in atTop, conditionalMeanSquare (g j) ≤ C * (Y j : ℝ) ^ α)
    (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (1 - α) / 2 ≤ ρ.re ∧ ρ.re ≤ (1 + α) / 2 := by
  have hright (s : ℂ) (hsz : riemannZeta s = 0)
      (hslt : s.re < 1) : s.re ≤ (1 + α) / 2 := by
    by_contra h
    have hs : 1 / 2 < s.re := by linarith [lt_of_not_ge h]
    have hsne : s ≠ 1 := by intro he; simp [he] at hslt
    exact zeta_ne_zero_of_sparse_polynomial_approximate_heads
      A hA g Y hg hY hhead α C hbound s hs hsne (by linarith [lt_of_not_ge h]) hsz
  have href := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hr := hright (Zeta23.reflect ρ) href.1 href.2.2
  have hl := hright ρ hz h1
  simp [Zeta23.reflect] at hr
  constructor <;> linarith

/-- The truncated weighted error is bounded by the genuine full error. -/
theorem conditionalHeadError_le_conditionalMeanError
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (N : ℕ)
    {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A) :
    conditionalHeadError N g ≤ conditionalMeanError g := by
  have hs := conditionalMeanError_summable_of_energy
    (legal_conditionalMeanSquare_summable A hA hg)
  exact sum_le_hasSum (Finset.range N)
    (fun k _ => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _)) hs.hasSum


end RiemannResearch.RH.Pareto
