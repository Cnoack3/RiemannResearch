/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalMeanApproximateHeads

/-!
# Regularized soft-head approximation and RH

Source: user-requested continuation of the RH program. The argument below is
derived from ConditionalMeanApproximateHeads, retaining the actual legal span,
conditional-mean energy, and signed Mellin annihilation.

The cost is head error + N^(-alpha) times the full conditional-mean energy.
A hypothetical zero with Re(s)>1/2 forces a uniform positive lower bound on
this cost for alpha < 2 Re(s)-1. Arbitrarily small costs at arbitrarily large
scales, for every positive alpha, therefore imply actual mathlib RH.

This is a conditional research reduction. The arithmetic feasibility property
ArbitrarilySmallRegularizedHeads is not proved. Existing full conditional-mean
approximation is shown to imply that property; no converse density theorem or
RH equivalence is asserted.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative

/-- A soft head fit penalized by the complete conditional-mean energy. -/
def regularizedHeadCost (α : ℝ) (N : ℕ) (g : ℕ → ℝ) : ℝ :=
  conditionalHeadError N g + (N : ℝ) ^ (-α) * conditionalMeanSquare g

theorem regularizedHeadCost_nonneg (α : ℝ) (N : ℕ) (g : ℕ → ℝ) :
    0 ≤ regularizedHeadCost α N g :=
  add_nonneg (conditionalHeadError_nonneg N g)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (conditionalMeanSquare_nonneg g))

/-- A hypothetical off-line zero obstructs every sufficiently large soft fit,
uniformly over all actual legal witnesses, at every exponent below its gap. -/
theorem regularizedHeadCost_obstruction_eventually
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (α : ℝ) (hα : α < 2 * s.re - 1) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ legalSeedSpan A,
      1 / (4 * (2 * conditionalMellinDualSquare s + 1)) ≤
        regularizedHeadCost α N g := by
  let ε : ℝ := 2 * s.re - 1 - α
  have hε : 0 < ε := by dsimp [ε]; linarith
  let K : ℝ := 3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)
  have hD := conditionalMellinDualSquare_nonneg s
  have hdecay := ((tendsto_rpow_neg_atTop hε).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (2 * K)
  have hsmall : ∀ᶠ N : ℕ in atTop, (2 * K) * (N : ℝ) ^ (-ε) ≤ 1 := by
    have hh : Tendsto (fun N : ℕ => (2 * K) * (N : ℝ) ^ (-ε)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero] using hdecay
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ h => h.le)
  filter_upwards [approximate_head_scaled_obstruction_eventually A hA s hs hs1 hz,
    hsmall, eventually_ge_atTop 1] with N hN hfactor hpos
  intro g hg
  have hnR : (0 : ℝ) < N := by exact_mod_cast hpos
  have hbase := hN g hg
  change (1 / 4 : ℝ) ≤
    2 * conditionalMellinDualSquare s * conditionalHeadError N g +
      2 * K * (N : ℝ) ^ (1 - 2 * s.re) * conditionalMeanSquare g at hbase
  have heq : ((2 * K) * (N : ℝ) ^ (-ε)) *
      ((N : ℝ) ^ (-α) * conditionalMeanSquare g) =
      2 * K * (N : ℝ) ^ (1 - 2 * s.re) * conditionalMeanSquare g := by
    calc
      _ = 2 * K * ((N : ℝ) ^ (-ε) * (N : ℝ) ^ (-α)) *
          conditionalMeanSquare g := by ring
      _ = _ := by
        rw [← Real.rpow_add hnR]
        have he : -ε + -α = 1 - 2 * s.re := by dsimp [ε]; ring
        rw [he]
  have hpen : 0 ≤ (N : ℝ) ^ (-α) * conditionalMeanSquare g :=
    mul_nonneg (Real.rpow_nonneg hnR.le _) (conditionalMeanSquare_nonneg g)
  have ht := mul_le_mul_of_nonneg_right hfactor hpen
  rw [heq, one_mul] at ht
  have hhead0 := conditionalHeadError_nonneg N g
  apply (div_le_iff₀ (by positivity : 0 < 4 * (2 * conditionalMellinDualSquare s + 1))).2
  unfold regularizedHeadCost
  nlinarith

/-- At arbitrarily large scales the actual regularized legal cost can be made
arbitrarily small, for every positive exponent. This is an open arithmetic target. -/
def ArbitrarilySmallRegularizedHeads (A : Set ℕ) : Prop :=
  ∀ α : ℝ, 0 < α → ∀ δ : ℝ, 0 < δ → ∀ N₀ : ℕ,
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ g ∈ legalSeedSpan A, regularizedHeadCost α N g < δ

theorem zeta_ne_zero_of_arbitrarilySmallRegularizedHeads
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hsmall : ArbitrarilySmallRegularizedHeads A)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hD := conditionalMellinDualSquare_nonneg s
  have hδ : 0 < 1 / (4 * (2 * conditionalMellinDualSquare s + 1)) := by positivity
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (regularizedHeadCost_obstruction_eventually A hA s hs hs1 hz
      (s.re - 1 / 2) (by linarith))
  obtain ⟨N, hN, g, hg, hcost⟩ := hsmall (s.re - 1 / 2) (by linarith)
    (1 / (4 * (2 * conditionalMellinDualSquare s + 1))) hδ N₀
  exact not_lt_of_ge (hN₀ N hN g hg) hcost

/-- A family-free soft quadratic approximation criterion for actual mathlib RH.
The arithmetic feasibility hypothesis is deliberately not asserted here. -/
theorem riemannHypothesis_of_arbitrarilySmallRegularizedHeads
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hsmall : ArbitrarilySmallRegularizedHeads A) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hright (s : ℂ) (hsz : riemannZeta s = 0)
      (hslt : s.re < 1) : s.re ≤ 1 / 2 := by
    by_contra h
    have hs : 1 / 2 < s.re := lt_of_not_ge h
    have hsne : s ≠ 1 := by intro he; simp [he] at hslt
    exact zeta_ne_zero_of_arbitrarilySmallRegularizedHeads A hA hsmall s hs hsne hsz
  have href := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hr := hright (Zeta23.reflect ρ) href.1 href.2.2
  have hl := hright ρ hz h1
  simp [Zeta23.reflect] at hr
  linarith
/-- Existing full conditional-mean approximation supplies the soft cost target.
The converse to density is not claimed; the proved reverse endpoint is RH. -/
theorem arbitrarilySmallRegularizedHeads_of_conditionalMeanApproximation
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (happrox : ∀ δ : ℝ, 0 < δ →
      ∃ g ∈ legalSeedSpan A, conditionalMeanError g < δ) :
    ArbitrarilySmallRegularizedHeads A := by
  intro α hα δ hδ N₀
  obtain ⟨g, hg, herr⟩ := happrox (δ / 2) (by linarith)
  have hdecay := ((tendsto_rpow_neg_atTop hα).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).mul_const (conditionalMeanSquare g)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-α) * conditionalMeanSquare g < δ / 2 := by
    have hh : Tendsto (fun N : ℕ => (N : ℝ) ^ (-α) * conditionalMeanSquare g)
        atTop (𝓝 0) := by
      simpa only [Function.comp_apply, zero_mul] using hdecay
    exact hh.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN, hcost⟩ := ((eventually_ge_atTop N₀).and hsmall).exists
  refine ⟨N, hN, g, hg, ?_⟩
  have hh := conditionalHeadError_le_conditionalMeanError A hA N hg
  unfold regularizedHeadCost
  linarith

end RiemannResearch.RH.Pareto
