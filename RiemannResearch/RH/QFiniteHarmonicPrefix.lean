/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QResolventHarmonicPrefix
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QHilbertConvergence
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FunProp

/-!
# Finite Gram criteria from matched projection displacements

Bagchi's Remark 8 identifies the squarefree dictionary, and his final section
uses finite Gram projections (https://arxiv.org/pdf/math/0607733). Here
the two Gram projections use the same finite dictionary in distinct norms.
The resulting one-sided tests concern their actual difference. Prefix
monotonicity permits a single finite stage at each good head with a uniform
allowance. No modulus for convergence of the projections is required.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement

open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity

/-- Freezing the physical head before sending the conductor cutoff to infinity
recovers the exact smaller signed mass. -/
theorem finite_minimumHarmonicPrefix_tendsto (X : ℕ) :
    Tendsto (fun M => minimumHarmonicPrefixOf (finiteDisplacement M) X)
      atTop (𝓝 (minimumHarmonicPrefix X)) := by
  have hc (s : ℝ) : Continuous (fun u : QHilbert => harmonicSideOf u s X) := by
    simp only [harmonicSideOf, ← qEvalCLM_apply]
    fun_prop
  exact (((hc 1).min (hc (-1))).tendsto displacement).comp finiteDisplacement_tendsto

theorem finite_minimumHarmonicPrefix_mono (M : ℕ) :
    Monotone (minimumHarmonicPrefixOf (finiteDisplacement M)) := by
  have hm (s : ℝ) : Monotone (harmonicSideOf (finiteDisplacement M) s) := by
    intro X Y hXY
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.add_le_add_right hXY 1))
    intro n _ _
    exact div_nonneg (le_max_right _ _) (Nat.cast_nonneg n)
  intro X Y hXY
  exact min_le_min (hm 1 hXY) (hm (-1) hXY)

/-- Different conductor subsequences may be used at different heads.
There is no rate assumption. -/
theorem riemannHypothesis_of_iterated_finite_harmonic_polylog
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∃ᶠ X : ℕ in atTop, ∃ᶠ M : ℕ in atTop,
      minimumHarmonicPrefixOf (finiteDisplacement M) X ≤ C * (Real.log (X : ℝ)) ^ B) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinal_harmonic_polylog B C hB hC
    (h.mono fun X hX => le_of_tendsto_of_frequently (finite_minimumHarmonicPrefix_tendsto X) hX)

/-- A single matched Gram pair may certify any growing number of checkpoints
on a prescribed cofinal physical grid. The grid can be arbitrarily sparse.
The stage only needs to escape with the checkpoint count. No comparison to
the physical size of the largest checkpoint is required. -/
theorem riemannHypothesis_of_finite_harmonic_grid
    (G : ℕ → ℕ) (hG : Tendsto G atTop atTop)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∃ᶠ K : ℕ in atTop, ∃ M : ℕ, K ≤ M ∧
      ∀ j : ℕ, j ≤ K →
        minimumHarmonicPrefixOf (finiteDisplacement M) (G j) ≤
          C * (Real.log (G j : ℝ)) ^ B) : RiemannHypothesis := by
  have hlim (j : ℕ) : minimumHarmonicPrefix (G j) ≤ C * (Real.log (G j : ℝ)) ^ B := by
    apply le_of_tendsto_of_frequently (finite_minimumHarmonicPrefix_tendsto (G j))
    apply frequently_atTop.mpr
    intro L
    obtain ⟨K, hK, M, hM, hgood⟩ := frequently_atTop.mp h (max j L)
    exact ⟨M, ((le_max_right j L).trans hK).trans hM, hgood j ((le_max_left j L).trans hK)⟩
  apply riemannHypothesis_of_cofinal_harmonic_polylog B C hB hC
  apply frequently_atTop.mpr
  intro L
  obtain ⟨j, hj⟩ := (hG.eventually (eventually_ge_atTop L)).exists
  exact ⟨G j, hj, hlim j⟩

/-- The uniform allowance can be imposed on just one sufficiently late
finite Gram pair per good window. Both coordinates must escape to infinity. -/
theorem minimumHarmonicPrefix_le_of_cofinal_finite_pairs (C : ℝ)
    (h : ∃ᶠ K : ℕ in atTop, ∃ M : ℕ, K ≤ M ∧
      minimumHarmonicPrefixOf (finiteDisplacement M) K ≤ C) (X : ℕ) :
    minimumHarmonicPrefix X ≤ C := by
  apply le_of_tendsto_of_frequently (finite_minimumHarmonicPrefix_tendsto X)
  apply frequently_atTop.mpr
  intro L
  obtain ⟨K, hK, M, hM, hgood⟩ := frequently_atTop.mp h (max X L)
  exact ⟨M, ((le_max_right X L).trans hK).trans hM,
    (finite_minimumHarmonicPrefix_mono M ((le_max_left X L).trans hK)).trans hgood⟩

/-- A two-solve test with a single finite conductor stage per good window.
Even the successively chosen signs may differ. -/
theorem riemannHypothesis_of_cofinal_finite_pairs (C : ℝ) (hC : 0 ≤ C)
    (h : ∃ᶠ K : ℕ in atTop, ∃ M : ℕ, K ≤ M ∧
      minimumHarmonicPrefixOf (finiteDisplacement M) K ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_harmonic_polylog 0 C le_rfl hC
  simpa only [Real.rpow_zero, mul_one] using
    (Eventually.of_forall (minimumHarmonicPrefix_le_of_cofinal_finite_pairs C h)).frequently

/-- The faithful residual vanishes exactly when cofinally many nested head/stage
pairs pass the fixed unit budget. The number one can be fixed in advance. -/
theorem residual_zero_iff_cofinal_finite_pairs :
    limitingResidual = 0 ↔
      ∃ᶠ K : ℕ in atTop, ∃ M : ℕ, K ≤ M ∧
        minimumHarmonicPrefixOf (finiteDisplacement M) K ≤ 1 := by
  constructor
  · intro hr
    apply Eventually.frequently
    apply Eventually.of_forall
    intro K
    have hz : minimumHarmonicPrefix K = 0 := by
      simp [minimumHarmonicPrefix, harmonicSide, displacement_eq_zero_of_residual_eq_zero hr,
        show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear]
    have ht := finite_minimumHarmonicPrefix_tendsto K
    rw [hz] at ht
    obtain ⟨M, hMK, hsmall⟩ :=
      ((eventually_ge_atTop K).and (ht.eventually (gt_mem_nhds zero_lt_one))).exists
    exact ⟨M, hMK, hsmall.le⟩
  · intro h
    apply (residual_zero_iff_fixed_cofinal_harmonic_polylog 0 1 le_rfl zero_le_one).mpr
    simpa only [Real.rpow_zero, mul_one] using
      (Eventually.of_forall (minimumHarmonicPrefix_le_of_cofinal_finite_pairs 1 h)).frequently

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
