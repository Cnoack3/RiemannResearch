/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalMeanHeadObstruction

/-!
# Subpolynomial conditional-mean exact heads imply RH

The family in the hypothesis is not constructed here. This theorem proves the
precise sufficient reduction, including cofinal subsequences and the exact
polynomial obstruction attached to a hypothetical right-half-plane zero.
-/
noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro

/-- The explicit polynomial lower bound from the conversation. -/
theorem exact_head_polynomial_obstruction_eventually (A : Set ℕ)
    (hA : ∀ a ∈ A, 0 < a) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ legalSeedSpan A,
      (∀ n, 0 < n → n ≤ N → g n = 1) →
      ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
        (N : ℝ) ^ (2 * s.re - 1) ≤ conditionalMeanSquare g := by
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hsadd : s + 1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h
    linarith
  have hB : 0 < ‖s * (s + 1)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hs0 hsadd))
  filter_upwards [exact_head_scaled_obstruction_eventually A hA s hs hs1 hz,
    eventually_ge_atTop 1] with N hob hN
  intro g hg hhead
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (1 - 2 * s.re) * (N : ℝ) ^ (2 * s.re - 1) = 1 := by
    rw [← Real.rpow_add hnR]
    convert Real.rpow_zero (N : ℝ) using 1 <;> congr 1 <;> ring
  have hc : (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
      ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) = (1 / 4 : ℝ) := by
    field_simp [ne_of_gt hd, ne_of_gt hB]
    ring
  have he : ((3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
      (N : ℝ) ^ (1 - 2 * s.re)) *
      (((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
        (N : ℝ) ^ (2 * s.re - 1)) = (1 / 4 : ℝ) := by
    calc
      _ = ((3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
          ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2))) *
          ((N : ℝ) ^ (1 - 2 * s.re) * (N : ℝ) ^ (2 * s.re - 1)) := by ring
      _ = _ := by rw [hc, hpow, mul_one]
  have hcoef : 0 < (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
      (N : ℝ) ^ (1 - 2 * s.re) := by positivity
  by_contra hnot
  have hbad := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) hcoef
  rw [he] at hbad
  exact not_lt_of_ge (hob g hg hhead) hbad

/-- Growth is measured only along the actual cofinal sequence of legal witnesses. -/
def SubpolynomialConditionalMean (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ j : ℕ in atTop, conditionalMeanSquare (g j) ≤ C * (Y j : ℝ) ^ ε

/-- The exact arithmetic zero obstruction excludes all right-half-plane zeros. -/
theorem zeta_ne_zero_of_subpolynomial_conditionalMean_heads
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = 1)
    (hY : Tendsto Y atTop atTop) (hsub : SubpolynomialConditionalMean g Y)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  let ε : ℝ := s.re - 1 / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := hsub ε hε
  let K : ℝ := 3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hK : 0 ≤ K :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hd.le
  have hyR : Tendsto (fun j => (Y j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hY
  have hdecay := ((tendsto_rpow_neg_atTop hε).comp hyR).const_mul (K * C)
  have hsmall : ∀ᶠ j : ℕ in atTop, (K * C) * (Y j : ℝ) ^ (-ε) < 1 / 4 :=
    hdecay.eventually (gt_mem_nhds (by norm_num : (K * C) * (0 : ℝ) < 1 / 4))
  have hob := hY.eventually (exact_head_scaled_obstruction_eventually A hA s hs hs1 hz)
  have hpos := hY.eventually (eventually_ge_atTop 1)
  obtain ⟨j, hj, hjbound, hjpos, hjsmall⟩ :=
    (hob.and (hbound.and (hpos.and hsmall))).exists
  have hypos : (0 : ℝ) < Y j := by exact_mod_cast hjpos
  have hbase := hj (g j) (hg j) (hhead j)
  change (1 / 4 : ℝ) ≤ K * (Y j : ℝ) ^ (1 - 2 * s.re) * conditionalMeanSquare (g j) at hbase
  have hupper : K * (Y j : ℝ) ^ (1 - 2 * s.re) * conditionalMeanSquare (g j) ≤
      (K * (Y j : ℝ) ^ (1 - 2 * s.re)) * (C * (Y j : ℝ) ^ ε) :=
    mul_le_mul_of_nonneg_left hjbound
      (mul_nonneg hK (Real.rpow_nonneg hypos.le _))
  have heq : (K * (Y j : ℝ) ^ (1 - 2 * s.re)) * (C * (Y j : ℝ) ^ ε) =
      (K * C) * (Y j : ℝ) ^ (-ε) := by
    calc
      _ = (K * C) * ((Y j : ℝ) ^ (1 - 2 * s.re) * (Y j : ℝ) ^ ε) := by ring
      _ = _ := by
        rw [← Real.rpow_add hypos]
        congr 2
        dsimp [ε]
        ring
  rw [heq] at hupper
  exact not_lt_of_ge (hbase.trans hupper) hjsmall

/-- Actual mathlib RH from the weaker, subpolynomial conditional-mean energy bound. -/
theorem riemannHypothesis_of_subpolynomial_conditionalMean_heads
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = 1)
    (hY : Tendsto Y atTop atTop) (hsub : SubpolynomialConditionalMean g Y) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hright (s : ℂ) (hsz : riemannZeta s = 0)
      (hs0 : 0 < s.re) (hslt : s.re < 1) : s.re ≤ 1 / 2 := by
    by_contra h
    have hs : 1 / 2 < s.re := lt_of_not_ge h
    have hsne : s ≠ 1 := by intro he; simp [he] at hslt
    exact zeta_ne_zero_of_subpolynomial_conditionalMean_heads A hA g Y hg hhead hY hsub
      s hs hsne hsz
  have href := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hr := hright (Zeta23.reflect ρ) href.1 href.2.1 href.2.2
  have hl := hright ρ hz h0 h1
  simp [Zeta23.reflect] at hr
  linarith

/-- Uniformly bounded conditional-mean energy is a special case of the subpolynomial bound. -/
theorem riemannHypothesis_of_bounded_conditionalMean_heads
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = 1)
    (hY : Tendsto Y atTop atTop) (C : ℝ)
    (hbound : ∀ j, conditionalMeanSquare (g j) ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_subpolynomial_conditionalMean_heads A hA g Y hg hhead hY
  have hC : 0 ≤ C := (conditionalMeanSquare_nonneg (g 0)).trans (hbound 0)
  intro ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hY.eventually (eventually_ge_atTop 1)] with j hj
  have hjR : (1 : ℝ) ≤ Y j := by exact_mod_cast hj
  have hp := Real.one_le_rpow hjR hε.le
  exact (hbound j).trans (by nlinarith)

end RiemannResearch.RH.Pareto
