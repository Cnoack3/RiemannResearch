/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.TreeEulerCriterion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Removing finitely many prime directions from the signed Euler tree

Forbidding finitely many primes in every leaf removes exactly their Euler
factors from the right-half-plane germ. Each factor is an analytic unit
where Re(s)>0. Consequently the pruned tree gives an equivalent RH test. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.PrimeTreeEuler

/-- Keep only the leaves whose set of included primes is disjoint from B. -/
def PrunedRootExtends (B : Finset ℕ) : Prop :=
  ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | (1 / 2 : ℝ) < s.re} ∧
    ∀ s : ℂ, 1 < s.re →
      Tendsto (fun n : ℕ => treeRoot (Nat.primesBelow n \ B) s) atTop (𝓝 (F s))

theorem treeRoot_mul_sdiff {B P : Finset ℕ} (h : B ⊆ P) (s : ℂ) :
    treeRoot B s * treeRoot (P \ B) s = treeRoot P s := by
  simp only [treeRoot_eq_product]
  simpa only [Finset.inter_eq_right.mpr h] using
    Finset.prod_inter_mul_prod_sdiff P B (fun p : ℕ => 1 - (p : ℂ) ^ (-s))

theorem analyticAt_treeRoot (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
    (s : ℂ) : AnalyticAt ℂ (treeRoot B) s := by
  simp_rw [funext (treeRoot_eq_product B)]
  apply B.analyticAt_fun_prod
  intro p hp
  have hn : (p : ℂ) ≠ 0 := by exact_mod_cast (hB p hp).ne_zero
  have hd : Differentiable ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) :=
    differentiable_id.neg.const_cpow (.inl hn)
  exact analyticAt_const.sub (hd.analyticAt s)

theorem treeRoot_ne_zero (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
    {s : ℂ} (hs : 0 < s.re) : treeRoot B s ≠ 0 := by
  rw [treeRoot_eq_product, Finset.prod_ne_zero_iff]
  intro p hp
  have hpr := hB p hp
  have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hpr.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpr.one_lt) (by linarith)
  apply sub_ne_zero.mpr
  intro he
  rw [← he, norm_one] at hnorm
  exact (lt_irrefl _ hnorm)

private theorem eventually_subset_primesBelow (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime) :
    ∀ᶠ n : ℕ in atTop, B ⊆ Nat.primesBelow n := by
  have h : ∀ᶠ n : ℕ in atTop, ∀ p ∈ B, p ∈ Nat.primesBelow n := by
    apply B.eventually_all.mpr
    intro p hp
    filter_upwards [eventually_gt_atTop p] with n hn
    exact Nat.mem_primesBelow.mpr ⟨hn, hB p hp⟩
  exact h

theorem rootExtends_iff_prunedRootExtends (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime) : RootExtends ↔ PrunedRootExtends B := by
  constructor
  · rintro ⟨F, hF, hlim⟩
    refine ⟨fun s => F s / treeRoot B s, ?_, ?_⟩
    · intro s hs
      have hs' : (1 / 2 : ℝ) < s.re := hs
      exact (hF s hs).div (analyticAt_treeRoot B hB s) (treeRoot_ne_zero B hB (by linarith))
    · intro s hs
      have hn : treeRoot B s ≠ 0 := treeRoot_ne_zero B hB (by linarith)
      apply Tendsto.congr' _ ((hlim s hs).div_const (treeRoot B s))
      filter_upwards [eventually_subset_primesBelow B hB] with n hsub
      apply (div_eq_iff hn).mpr
      rw [mul_comm, treeRoot_mul_sdiff hsub]
  · rintro ⟨F, hF, hlim⟩
    refine ⟨fun s => treeRoot B s * F s, ?_, ?_⟩
    · intro s hs
      exact (analyticAt_treeRoot B hB s).mul (hF s hs)
    · intro s hs
      apply Tendsto.congr' _ ((hlim s hs).const_mul (treeRoot B s))
      filter_upwards [eventually_subset_primesBelow B hB] with n hsub
      exact treeRoot_mul_sdiff hsub s

theorem riemannHypothesis_iff_finitelyPrunedRootExtends (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime) : RiemannHypothesis ↔ PrunedRootExtends B :=
  riemannHypothesis_iff_rootExtends.trans (rootExtends_iff_prunedRootExtends B hB)

end RiemannResearch.RH.PrimeTreeEuler
