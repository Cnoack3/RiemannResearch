/-
Vendored from anthropics/formal-math, zeta23, commit
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844.
Local modification (2026-09-07): intra-project imports relocated under
RiemannResearch.RH.WeilExplicitFormula; declarations and namespaces unchanged.
Original copyright notices and Apache-2.0 license are preserved.
-/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/CountByIntegral.lean — the zero count as a contour integral, specialised to Λ.
Used by Zeta23/RvM/Statement.lean and MainTerm.lean (the symmetry fold and the Γ-side).

MAIN RESULT `rectangleIntegral'_logDeriv_completedZeta_eq_Ncount`: for 0 < T₁ ≤ T₂, neither the
ordinate of a nontrivial zero,
    (1/2πi) ∮_{∂([−1,2]×[T₁,T₂])} Λ'/Λ(s) ds = N(T₁,T₂)        (Λ = completedRiemannZeta),
where N = Zeta23.Ncount counts nontrivial zeros of Mathlib's riemannZeta with T₁ < γ ≤ T₂ with
multiplicity zeroMult = analyticOrderAt ζ. Ingredients (proved from Mathlib here and in RvM/CompletedZeta):
 • Λ is analytic off {0,1}; Λ = Gammaℝ·ζ with Gammaℝ ≠ 0 on Re s > 0, so on the strip the zeros
   and their analytic orders agree with ζ's; Λ ≠ 0 for Re s ≥ 1 (Mathlib's non-vanishing of ζ)
   and, by Λ(1−s) = Λ(s), for Re s ≤ 0; hence {Λ = 0} = nontrivial zeros of ζ exactly.
 • Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (weighted argument principle, g ≡ 1).
-/
import RiemannResearch.RH.WeilExplicitFormula.Analytic.RectangleLogDeriv
import RiemannResearch.RH.WeilExplicitFormula.RvM.CompletedZeta
import RiemannResearch.RH.WeilExplicitFormula.Statement.SeamClosed
import Mathlib.Tactic.FunProp

open Complex Set Topology Filter Real
open scoped BigOperators

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Λ = completedRiemannZeta: analyticity, relation to ζ, zeros -/

/-- On the open right half-plane (away from 1) the analytic order of Λ equals zeroMult = the
analytic order of ζ. -/
lemma analyticOrderNatAt_completedRiemannZeta {ρ : ℂ} (h : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderNatAt completedRiemannZeta ρ = zeroMult ρ := by
  have h0 : ρ ≠ 0 := fun h' => by simp [h'] at h
  have hev : riemannZeta =ᶠ[𝓝 ρ] (completedRiemannZeta * fun s => (Gammaℝ s)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h0] with s hs
    rw [Pi.mul_apply, riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
  have hΛ := analyticAt_completedRiemannZeta h0 h1
  have hGinv : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ := differentiable_Gammaℝ_inv.analyticAt ρ
  have hG0 : analyticOrderAt (fun s => (Gammaℝ s)⁻¹) ρ = 0 :=
    hGinv.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h))
  unfold zeroMult analyticOrderNatAt
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hΛ hGinv, hG0, add_zero]

/-! ## The count -/

/-- **N(T₁,T₂) as a contour integral.** For 0 < T₁ ≤ T₂ with no nontrivial zero of ordinate T₁ or
T₂:  (1/2πi)∮_{∂([−1,2]×[T₁,T₂])} Λ'/Λ = Ncount T₁ T₂. -/
theorem rectangleIntegral'_logDeriv_completedZeta_eq_Ncount {T₁ T₂ : ℝ} (hT₁ : 0 < T₁)
    (hT : T₁ ≤ T₂) (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂) :
    RectangleIntegral' (logDeriv completedRiemannZeta) (-1 + T₁ * I) (2 + T₂ * I)
      = (Ncount T₁ T₂ : ℂ) := by
  classical
  set z : ℂ := -1 + T₁ * I with hzdef
  set w : ℂ := 2 + T₂ * I with hwdef
  have hzre : z.re = -1 := by simp [z]
  have hzim : z.im = T₁ := by simp [z]
  have hwre : w.re = 2 := by simp [w]
  have hwim : w.im = T₂ := by simp [w]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; norm_num
  have him : z.im ≤ w.im := by rw [hzim, hwim]; exact hT
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (-1 ≤ s.re ∧ s.re ≤ 2) ∧ (T₁ ≤ s.im ∧ s.im ≤ T₂) := by
    intro s
    simp only [Rectangle, mem_reProdIm, hzre, hzim, hwre, hwim,
      uIcc_of_le (show (-1 : ℝ) ≤ 2 by norm_num), uIcc_of_le hT, mem_Icc]
  have hf : AnalyticOnNhd ℂ completedRiemannZeta (Rectangle z w) := by
    intro s hs
    have hi : 0 < s.im := by linarith [((hmem s).mp hs).2.1]
    exact analyticAt_completedRiemannZeta (fun h => by simp [h] at hi) (fun h => by simp [h] at hi)
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (Rectangle z w) := fun _ _ => analyticAt_const
  have hfin := zetaSeam.finite_window T₁ T₂
  have hZ : ∀ s ∈ Rectangle z w, completedRiemannZeta s = 0 ↔ s ∈ hfin.toFinset := by
    intro s hs
    rw [Set.Finite.mem_toFinset]
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hs
    rw [completedRiemannZeta_eq_zero_iff]
    constructor
    · intro hnz
      exact ⟨hnz, lt_of_le_of_ne hi1 (fun h' => hgood₁ s hnz h'.symm), hi2⟩
    · rintro ⟨hnz, _⟩
      exact hnz
  have hZsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs
    obtain ⟨⟨_, h1, h2⟩, hi1, hi2⟩ := hs
    exact (hmem s).mpr ⟨⟨by linarith, by linarith⟩, hi1.le, hi2⟩
  have hborder : ∀ s ∈ RectangleBorder z w, completedRiemannZeta s ≠ 0 := by
    intro s hs h0
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp (rectangleBorder_subset_rectangle z w hs)
    have hnz := completedRiemannZeta_eq_zero_iff.mp h0
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, hzre, hzim, hwre,
      hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood₁ s hnz h'
    · linarith [hnz.2.1]
    · exact hgood₂ s hnz h'
    · linarith [hnz.2.2]
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hf hg hborder
    hfin.toFinset hZ hZsub
  simp only [one_mul, mul_one] at key
  rw [show (fun s => logDeriv completedRiemannZeta s) = logDeriv completedRiemannZeta from rfl]
    at key
  rw [key]
  unfold Ncount
  have hset : zerosIn T₁ T₂ = {ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂} := by
    ext ρ; simp [zerosIn]
  rw [hset, finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  rw [Set.Finite.mem_toFinset] at hρ
  obtain ⟨⟨_, h1, h2⟩, _⟩ := hρ
  rw [analyticOrderNatAt_completedRiemannZeta h1 (fun h' => by simp [h'] at h2)]

/-! ## Weighted actual-zero contour identity

This extends the preceding actual zero-count proof to an analytic weight and
variable rectangle width. All ordinary analyticity and boundary conditions
are explicit. The centered exponential result is an exact equality; a uniform
Landau estimate remains a separate analytic obligation.
-/

/-- Weighted argument principle for the actual completed zeta function, with
all actual multiplicities retained, on [1-c,c] x [T1,T2]. -/
theorem rectangleIntegral'_mul_logDeriv_completedZeta_eq_zero_sum
    {T₁ T₂ c : ℝ} (hc : 1 < c) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    RectangleIntegral' (fun s => g s * logDeriv completedRiemannZeta s)
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
  have hf : AnalyticOnNhd ℂ completedRiemannZeta (Rectangle z w) := by
    intro s hs
    have hi : 0 < s.im := by linarith [((hmem s).mp hs).2.1]
    exact analyticAt_completedRiemannZeta
      (fun h => by simp [h] at hi) (fun h => by simp [h] at hi)
  have hga : AnalyticOnNhd ℂ g (Rectangle z w) := fun s _ => hg.analyticAt s
  have hfin := zetaSeam.finite_window T₁ T₂
  have hZ : ∀ s ∈ Rectangle z w,
      completedRiemannZeta s = 0 ↔ s ∈ hfin.toFinset := by
    intro s hs
    rw [Set.Finite.mem_toFinset]
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hs
    rw [completedRiemannZeta_eq_zero_iff]
    constructor
    · intro hnz
      exact ⟨hnz, lt_of_le_of_ne hi1
        (fun h' => hgood₁ s hnz h'.symm), hi2⟩
    · rintro ⟨hnz, _⟩
      exact hnz
  have hZsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs
    obtain ⟨⟨_, h1, h2⟩, hi1, hi2⟩ := hs
    exact (hmem s).mpr ⟨⟨by linarith, by linarith⟩, hi1.le, hi2⟩
  have hborder : ∀ s ∈ RectangleBorder z w,
      completedRiemannZeta s ≠ 0 := by
    intro s hs h0
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ :=
      (hmem s).mp (rectangleBorder_subset_rectangle z w hs)
    have hnz := completedRiemannZeta_eq_zero_iff.mp h0
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      hzre, hzim, hwre, hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood₁ s hnz h'
    · linarith [hnz.2.1]
    · exact hgood₂ s hnz h'
    · linarith [hnz.2.2]
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv
    hre him hf hga hborder hfin.toFinset hZ hZsub
  rw [key]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  rw [Set.Finite.mem_toFinset] at hρ
  obtain ⟨⟨_, h1, h2⟩, _⟩ := hρ
  rw [analyticOrderNatAt_completedRiemannZeta h1
    (fun h' => by simp [h'] at h2)]

/-- Centered exponential specialization of the exact weighted contour identity.
No bound for this contour integral is asserted. -/
theorem rectangleIntegral'_centered_exp_logDeriv_completedZeta_eq_zero_sum
    {T₁ T₂ c : ℝ} (hc : 1 < c) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂) (u : ℝ) :
    RectangleIntegral'
        (fun s => Complex.exp ((u : ℂ) * (s - 1 / 2)) *
          logDeriv completedRiemannZeta s)
        ((1 - c : ℝ) + T₁ * I) ((c : ℝ) + T₂ * I)
      = ∑ ρ ∈ (zetaSeam.finite_window T₁ T₂).toFinset,
          (zeroMult ρ : ℂ) * Complex.exp ((u : ℂ) * (ρ - 1 / 2)) := by
  exact rectangleIntegral'_mul_logDeriv_completedZeta_eq_zero_sum
    hc hT₁ hT hgood₁ hgood₂
    (fun s => Complex.exp ((u : ℂ) * (s - 1 / 2))) (by fun_prop)


end RvM
end Zeta23
