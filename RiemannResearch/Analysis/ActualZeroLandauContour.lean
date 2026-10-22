/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.RH.WeilExplicitFormula.Analytic.RectangleLogDeriv
import Mathlib.Tactic.FunProp

/-!
# Exact exponential contours for the actual Riemann zeta function

The weighted argument principle retains every actual analytic multiplicity.
The ordinary contour geometry, horizontal zero avoidance and analyticity of
its weight are explicit. The centered exponential specialization is the exact
starting identity for a rational-frequency Landau estimate.

Proof adapted from RvM/CountByIntegral.lean and the existing proved
ActualZeroOrdinate.positive_zero_in_strip. Ford--Zaharescu, Lemma 1,
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf, supports the intended
Landau contour strategy, not a claim that its quantitative estimate is proved
here. FiniteOscillatoryKernel.lean supplies the exact right-side kernels.
-/

open Complex Set Topology Filter Real
open scoped BigOperators

noncomputable section

namespace Zeta23
namespace RvM

/-- Weighted argument principle for the actual Riemann zeta function on
the positive-height rectangle [1-c,c] x [T1,T2]. -/
theorem rectangleIntegral'_mul_logDeriv_riemannZeta_eq_zero_sum
    {T₁ T₂ c : ℝ} (hc : 1 < c) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    RectangleIntegral' (fun s => g s * logDeriv riemannZeta s)
        ((1 - c : ℝ) + T₁ * I) ((c : ℝ) + T₂ * I)
      = ∑ ρ ∈ (zetaSeam.finite_window T₁ T₂).toFinset,
          (zeroMult ρ : ℂ) * g ρ := by
  classical
  set z : ℂ := (1 - c : ℝ) + T₁ * I with hzdef
  set w : ℂ := (c : ℝ) + T₂ * I with hwdef
  have hzre : z.re = 1 - c := by simp [z]
  have hzim : z.im = T₁ := by simp [z]
  have hwre : w.re = c := by simp [w]
  have hwim : w.im = T₂ := by simp [w]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have him : z.im ≤ w.im := by rw [hzim, hwim]; exact hT
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (1 - c ≤ s.re ∧ s.re ≤ c) ∧ (T₁ ≤ s.im ∧ s.im ≤ T₂) := by
    intro s
    simp only [Rectangle, mem_reProdIm, hzre, hzim, hwre, hwim,
      uIcc_of_le (show (1 - c : ℝ) ≤ c by linarith), uIcc_of_le hT, mem_Icc]
  have hf : AnalyticOnNhd ℂ riemannZeta (Rectangle z w) := by
    intro s hs
    have hi : 0 < s.im := by linarith [((hmem s).mp hs).2.1]
    have hs1 : s ≠ 1 := fun h => by simp [h] at hi
    refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with q hq
    exact differentiableAt_riemannZeta hq
  have hga : AnalyticOnNhd ℂ g (Rectangle z w) := fun s _ => hg.analyticAt s
  have hfin := zetaSeam.finite_window T₁ T₂
  have hZ : ∀ s ∈ Rectangle z w,
      riemannZeta s = 0 ↔ s ∈ hfin.toFinset := by
    intro s hs
    rw [Set.Finite.mem_toFinset]
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hs
    constructor
    · intro hzero
      have hnz := RiemannResearch.Analysis.ActualZeroOrdinate.positive_zero_in_strip
        hzero (by linarith)
      exact ⟨hnz, lt_of_le_of_ne hi1
        (fun h' => hgood₁ s hnz h'.symm), hi2⟩
    · rintro ⟨hnz, _⟩
      exact hnz.1
  have hZsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs
    obtain ⟨⟨_, h1, h2⟩, hi1, hi2⟩ := hs
    exact (hmem s).mpr ⟨⟨by linarith, by linarith⟩, hi1.le, hi2⟩
  have hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0 := by
    intro s hs hzero
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ :=
      (hmem s).mp (rectangleBorder_subset_rectangle z w hs)
    have hnz := RiemannResearch.Analysis.ActualZeroOrdinate.positive_zero_in_strip
      hzero (by linarith)
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      hzre, hzim, hwre, hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood₁ s hnz h'
    · linarith [hnz.2.1]
    · exact hgood₂ s hnz h'
    · linarith [hnz.2.2]
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv
    hre him hf hga hborder hfin.toFinset hZ hZsub
  simpa only [analyticOrderNatAt, zeroMult] using key

/-- Centered exponential specialization; every actual multiplicity is retained. -/
theorem rectangleIntegral'_centered_exp_logDeriv_riemannZeta_eq_zero_sum
    {T₁ T₂ c : ℝ} (hc : 1 < c) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂) (u : ℝ) :
    RectangleIntegral'
        (fun s => Complex.exp ((u : ℂ) * (s - 1 / 2)) * logDeriv riemannZeta s)
        ((1 - c : ℝ) + T₁ * I) ((c : ℝ) + T₂ * I)
      = ∑ ρ ∈ (zetaSeam.finite_window T₁ T₂).toFinset,
          (zeroMult ρ : ℂ) * Complex.exp ((u : ℂ) * (ρ - 1 / 2)) := by
  exact rectangleIntegral'_mul_logDeriv_riemannZeta_eq_zero_sum
    hc hT₁ hT hgood₁ hgood₂
    (fun s => Complex.exp ((u : ℂ) * (s - 1 / 2))) (by fun_prop)

end RvM
end Zeta23
