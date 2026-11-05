/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import RiemannResearch.RH.BurnolCayleyJensen
import RiemannResearch.RH.ChebyshevMellinRH

/-! # The holomorphic extension criterion for the signed prime tree

Each leaf of a finite binary prime tree is a subset of the primes below the
cutoff. Including a prime p multiplies its weight by -p^(-s), and excluding
it multiplies the weight by 1. The criterion only takes limits on Re(s)>1.
It asks whether the resulting root function extends holomorphically.

Source: NIST Digital Library of Mathematical Functions, Euler product,
https://dlmf.nist.gov/25.2.E11 . -/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.PrimeTreeEuler

open RiemannResearch.RH.Burnol

/-- Sum of signed leaf weights in a finite binary prime tree. -/
def treeRoot (P : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ T ∈ P.powerset, ∏ p ∈ T, (-((p : ℂ) ^ (-s)))

theorem treeRoot_eq_product (P : Finset ℕ) (s : ℂ) :
    treeRoot P s = ∏ p ∈ P, (1 - (p : ℂ) ^ (-s)) := by
  simpa only [treeRoot, sub_eq_add_neg] using
    (Finset.prod_one_add (f := fun p : ℕ => -((p : ℂ) ^ (-s))) P).symm

/-- Contracting the two branches at a new prime. -/
theorem treeRoot_insert (P : Finset ℕ) (p : ℕ) (hp : p ∉ P) (s : ℂ) :
    treeRoot (insert p P) s =
      treeRoot P s + (-((p : ℂ) ^ (-s))) * treeRoot P s := by
  rw [treeRoot_eq_product, Finset.prod_insert hp, treeRoot_eq_product]
  ring

theorem tendsto_treeRoot {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n : ℕ => treeRoot (Nat.primesBelow n) s) atTop
      (𝓝 (riemannZeta s)⁻¹) := by
  have h := (riemannZeta_eulerProduct hs).inv₀ (riemannZeta_ne_zero_of_one_le_re hs.le)
  simpa only [treeRoot_eq_product, Finset.prod_inv_distrib, inv_inv, Function.comp_apply]
    using h

/-- Intrinsic statement in terms of the tree. No zeta function occurs here. -/
def RootExtends : Prop :=
  ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | (1 / 2 : ℝ) < s.re} ∧
    ∀ s : ℂ, 1 < s.re →
      Tendsto (fun n : ℕ => treeRoot (Nat.primesBelow n) s) atTop (𝓝 (F s))

private theorem ne_zero_of_half_lt {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    s ≠ 0 := by
  intro he
  norm_num [he] at hs

private theorem regularZetaRatio_ne_zero_of_rh (hRH : RiemannHypothesis)
    {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) : regularZetaRatio s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · simp
  have hz : riemannZeta s ≠ 0 := by
    by_cases hle : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re hle
    · intro he
      have hline := (riemannHypothesis_iff_strip_zeros_on_line.mp hRH)
        s he (by linarith) (lt_of_not_ge hle)
      linarith
  rw [regularZetaRatio_eq (by linarith) hs1]
  exact mul_ne_zero (div_ne_zero (sub_ne_zero.mpr hs1) (ne_zero_of_half_lt hs)) hz

theorem rootExtends_of_riemannHypothesis (hRH : RiemannHypothesis) :
    RootExtends := by
  refine ⟨fun s => ((s - 1) / s) / regularZetaRatio s, ?_, ?_⟩
  · intro s hs
    exact (((analyticAt_id.sub analyticAt_const).div analyticAt_id
        (ne_zero_of_half_lt hs)).div (analyticAt_regularZetaRatio (ne_zero_of_half_lt hs))
        (regularZetaRatio_ne_zero_of_rh hRH hs))
  · intro s hs
    have h0 : s ≠ 0 := ne_zero_of_half_lt (by linarith)
    have h1 : s ≠ 1 := by intro he; norm_num [he] at hs
    have hz := riemannZeta_ne_zero_of_one_le_re hs.le
    have hvalue : ((s - 1) / s) / regularZetaRatio s = (riemannZeta s)⁻¹ := by
      rw [regularZetaRatio_eq (by linarith) h1]
      field_simp [h0, sub_ne_zero.mpr h1, hz]
    change Tendsto _ atTop (𝓝 (((s - 1) / s) / regularZetaRatio s))
    rw [hvalue]
    exact tendsto_treeRoot hs

/-- The identity theorem propagates the initial tree identity across the
whole half-plane; regularZetaRatio removes the zeta pole at one. -/
theorem regularZetaRatio_mul_extension {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {s | (1 / 2 : ℝ) < s.re})
    (hlim : ∀ s : ℂ, 1 < s.re →
      Tendsto (fun n : ℕ => treeRoot (Nat.primesBelow n) s) atTop (𝓝 (F s)))
    {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    regularZetaRatio s * F s = (s - 1) / s := by
  have hl : AnalyticOnNhd ℂ (fun z => regularZetaRatio z * F z)
      {z | (1 / 2 : ℝ) < z.re} := by
    intro z hz
    exact (analyticAt_regularZetaRatio (ne_zero_of_half_lt hz)).mul (hF z hz)
  have hr : AnalyticOnNhd ℂ (fun z : ℂ => (z - 1) / z)
      {z | (1 / 2 : ℝ) < z.re} := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).div analyticAt_id (ne_zero_of_half_lt hz)
  have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have he : (fun z => regularZetaRatio z * F z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => (z - 1) / z) := by
    filter_upwards [ho.mem_nhds (x := (2 : ℂ)) (by norm_num)] with z hz
    have hright : 1 < z.re := hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hright
    have hfz := tendsto_nhds_unique (hlim z hright) (tendsto_treeRoot hright)
    rw [regularZetaRatio_eq (by linarith) h1, hfz, mul_assoc,
      mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_le_re hright.le), mul_one]
  exact (hl.eqOn_of_preconnected_of_eventuallyEq hr
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (z₀ := (2 : ℂ)) (by norm_num) he).eq_of_mem hs

/-- The root of the signed squarefree prime tree has a holomorphic extension
to Re(s)>1/2 if and only if Mathlib's Riemann hypothesis holds. -/
theorem riemannHypothesis_iff_rootExtends : RiemannHypothesis ↔ RootExtends := by
  refine ⟨rootExtends_of_riemannHypothesis, ?_⟩
  rintro ⟨F, hF, hlim⟩
  apply ChebyshevMellin.riemannHypothesis_iff_error_analytic.mpr
  intro s hs hlt
  have h0 := ne_zero_of_half_lt hs
  have h1 : s ≠ 1 := by intro he; norm_num [he] at hlt
  apply (ChebyshevMellin.analyticAt_meromorphicError_iff h0 h1).mpr
  intro hzeta
  have h := regularZetaRatio_mul_extension hF hlim hs
  rw [regularZetaRatio_eq (by linarith) h1, hzeta, mul_zero, zero_mul] at h
  exact (div_ne_zero (sub_ne_zero.mpr h1) h0) h.symm

end RiemannResearch.RH.PrimeTreeEuler
