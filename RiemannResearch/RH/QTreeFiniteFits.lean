/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrefixPruning
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QCompositeCarryDetection

/-! # Computing a fixed pruned tree budget by matched finite projections

Source: the November 2026 prime-tree handoff. Keep the finite projection index
and the conductor horizon separate. Only a fixed finite sum passes to the
limit, so this transfer requires no rate or diagonal uniformity. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeSubtreeBudget
open ZetaTwoHilbert QSquarefreeDisplacementRigidity QSquarefreeFiniteDisplacement

theorem fitted_charge_tendsto (m : ℕ) :
    Tendsto (fun j => charge (finiteDisplacement j) m) atTop (𝓝 (charge displacement m)) := by
  apply QCompositeCarryDetection.charge_tendsto_of_sites
  intro k _
  exact ⟨qSequence_tendsto_of_tendsto finiteDisplacement_tendsto k,
    qSequence_tendsto_of_tendsto finiteDisplacement_tendsto (k-1)⟩

theorem fitted_subtree_tendsto (H r : ℕ) :
    Tendsto (fun j => subtree (charge (finiteDisplacement j)) H r) atTop
      (𝓝 (subtree (charge displacement) H r)) := by
  unfold subtree
  apply tendsto_finsetSum
  intro m _
  by_cases hm : r ∈ prefixes m
  · simp only [if_pos hm]
    exact (fitted_charge_tendsto m).div_const _
  · simp only [if_neg hm]
    exact tendsto_const_nhds

/-- Finite signed pooling, the positive part, and finite fitting commute at
fixed head and horizon. -/
theorem fitted_prunedBudget_tendsto (σ : ℝ) (H N n : ℕ) :
    Tendsto (fun j => prunedBudget (subtree (charge (finiteDisplacement j)) H) σ H N n)
      atTop (𝓝 (prunedBudget (subtree (charge displacement) H) σ H N n)) := by
  unfold prunedBudget
  apply Tendsto.add <;> apply tendsto_finsetSum
  · intro r _
    by_cases hr : r ≤ N
    · simp only [if_pos hr]
      exact (tendsto_const_nhds.max ((fitted_subtree_tendsto H r).const_mul (-σ))).const_mul _
    · simp only [if_neg hr]
      exact tendsto_const_nhds
  · intro k _
    apply Tendsto.const_mul
    apply Tendsto.max tendsto_const_nhds
    apply Tendsto.const_mul
    unfold frontierMass
    apply tendsto_finsetSum
    intro r _
    by_cases hr : k = parent r ∧ N < r
    · simpa only [if_pos hr] using fitted_subtree_tendsto H r
    · simp only [if_neg hr]
      exact tendsto_const_nhds

/-- A common bad-sign budget, witnessed by arbitrarily large finite projection
stages at arbitrarily large conductor horizons for each fixed site, forces RH. -/
theorem riemannHypothesis_of_fitted_prunedBudget (σ C : ℝ) (hσ : |σ| = 1) (hC : 0 ≤ C)
    (hb : ∀ n, ∃ᶠ H : ℕ in atTop, ∃ᶠ j : ℕ in atTop,
      prunedBudget (subtree (charge (finiteDisplacement j)) H) σ H n n ≤ C) :
    RiemannHypothesis := by
  apply rh_of_pruned_subtree_budget σ C hσ hC
  intro n
  apply (hb n).mono
  intro H hj
  by_contra! h
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hj.and_eventually ((fitted_prunedBudget_tendsto σ H n n).eventually (lt_mem_nhds h))).exists
  exact (not_lt_of_ge hj₁) hj₂

end RiemannResearch.RH.QPrimeSubtreeBudget
