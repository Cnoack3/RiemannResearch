/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimeSubtreeBudget
import RiemannResearch.RH.PrefixNoEscape
import RiemannResearch.RH.PrefixPruning
import RiemannResearch.RH.MertensBaezDuarteConverse

/-! # The matched prime-prefix tree as a criterion for RH

The internal residual equivalence uses the fixed-coordinate signed tree limit.
The two RH equivalences explicitly take the published Báez-Duarte approximation
theorem in the form recorded in MertensBaezDuarteConverse. No reverse analytic
implication is promoted to an axiom. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeSubtreeBudget
open Pareto ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity

/-- The signed sum observed by a fixed physical integer. The same actual
displacement supplies all Möbius coefficients at all horizons. -/
def signedTreeReadout (H n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 H, stepDigit r n * subtree (charge displacement) H r

/-- The internal projection residual vanishes exactly when every physical
site observes a tree sum tending to zero. -/
theorem residual_zero_iff_tree_readout_tendsto_zero :
    limitingResidual = 0 ↔
      ∀ n : ℕ, Tendsto (fun H : ℕ => signedTreeReadout H n) atTop (𝓝 0) := by
  constructor
  · intro hr n
    have ht := signed_subtree_tendsto displacement n
    have hd : qSequence displacement n = 0 := by
      rw [displacement_eq_zero_of_residual_eq_zero hr]
      exact congrFun (show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear) n
    simpa only [signedTreeReadout, hd, neg_zero] using ht
  · intro he
    apply residual_eq_zero_of_displacement_physically_bounded 0
    intro n
    have ht : Tendsto (fun H : ℕ => signedTreeReadout H n) atTop
        (𝓝 (-qSequence displacement n)) := signed_subtree_tendsto displacement n
    have h0 : -qSequence displacement n = 0 := tendsto_nhds_unique ht (he n)
    simp [neg_eq_zero.mp h0]

/-- Báez-Duarte, Theorem 2, supplies the reverse mathematical input. -/
theorem riemannHypothesis_iff_tree_readout_tendsto_zero
    (hBD : BaezDuarte.BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔
      ∀ n : ℕ, Tendsto (fun H : ℕ => signedTreeReadout H n) atTop (𝓝 0) := by
  constructor
  · intro hRH
    exact residual_zero_iff_tree_readout_tendsto_zero.mp
      (QMertensFirstMoment.residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH)
  · intro he
    obtain ⟨C, hC⟩ := residual_eq_zero_iff_displacement_physically_bounded.mp
      (residual_zero_iff_tree_readout_tendsto_zero.mpr he)
    exact riemannHypothesis_of_displacement_bounded C hC

/-- The tree charge vanishes identically when the projection residual vanishes. -/
theorem subtree_eq_zero_of_residual_zero (hr : limitingResidual = 0) (H r : ℕ) :
    subtree (charge displacement) H r = 0 := by
  have hz : qSequence (0 : QHilbert) = 0 := map_zero qSequenceLinear
  simp [subtree, charge, displacement_eq_zero_of_residual_eq_zero hr, hz, mobiusDifference]

/-- A fixed sign and a fixed bound can be prescribed in advance. In the reverse
direction, the theorem used to prove RH assumes only a cofinal bound at each
physical site. In the forward direction all finite charges vanish. -/
theorem riemannHypothesis_iff_pruned_subtree_budget
    (hBD : BaezDuarte.BaezDuarteMobiusApproximation)
    (σ C : ℝ) (hσ : |σ| = 1) (hC : 0 ≤ C) :
    RiemannHypothesis ↔
      ∀ n : ℕ, ∃ᶠ H : ℕ in atTop,
        prunedBudget (subtree (charge displacement) H) σ H n n ≤ C := by
  constructor
  · intro hRH n
    have hr := QMertensFirstMoment.residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro H
    simpa [prunedBudget, frontierMass, subtree_eq_zero_of_residual_zero hr] using hC
  · exact rh_of_pruned_subtree_budget σ C hσ hC

/-- The local criterion in both directions with the published Báez-Duarte
approximation theorem supplied explicitly for the implication from RH. -/
theorem riemannHypothesis_iff_no_escape (hBD : BaezDuarte.BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔
      (∀ s : ℕ, 2 ≤ s →
        Tendsto (fun H : ℕ => subtree (charge displacement) H s) atTop (𝓝 0)) ∧
      (∀ r : ℕ, 2 ≤ r → ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, r ≤ K ∧
        ∀ᶠ H : ℕ in atTop, |escapingChildMass (charge displacement) r K H| ≤ ε) := by
  constructor
  · intro hRH
    have hr := QMertensFirstMoment.residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH
    constructor
    · intro s _
      simp [subtree_eq_zero_of_residual_zero hr]
    · intro r _ ε hε
      refine ⟨r, le_rfl, Filter.Eventually.of_forall fun H => ?_⟩
      simpa [escapingChildMass, subtree_eq_zero_of_residual_zero hr] using hε.le
  · rintro ⟨hnet, hesc⟩
    exact rh_of_no_escape hnet hesc

end RiemannResearch.RH.QPrimeSubtreeBudget
