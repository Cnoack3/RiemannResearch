/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PeriodicArithmeticCumulative
import RiemannResearch.RH.QWeightedResidueMaps
import RiemannResearch.RH.CRTSquarefreeConverse
/-!
# Legal periodic divisor-residue primitives

Source: user's weighted-CRT manuscript, 1 November 2026,
"The legal primitive spaces are smaller". Legality means the actual
zero-mean divisorResidueSpan. If the period is squarefree, every conductor
in this finite span is squarefree. The results also hold for general periods.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.SquarefreeWeightedPrimitives
open ArithmeticCumulative Pareto QWeightedResidues QWeightedResidueMaps QCesaroEnergy
open RiemannResearch.Analysis.FiniteWeightedRefinement
def IsLegalPrimitive (L : ℕ) (R : Fin L → ℝ) : Prop :=
  ∃ g : ℕ → ℝ, g ∈ divisorResidueSpan L ∧ cumulative g L = 0 ∧
    ∀ a : Fin L, R a = cumulative g a.val
theorem legalPrimitive_zero (L : ℕ) (hL : 0 < L) (R : Fin L → ℝ)
    (hR : IsLegalPrimitive L R) : R ⟨0, hL⟩ = 0 := by
  obtain ⟨g, _, _, h⟩ := hR
  simpa using h ⟨0, hL⟩
theorem legal_cumulative_periodic (g : ℕ → ℝ) (L : ℕ)
    (hg : g ∈ divisorResidueSpan L) (hz : cumulative g L = 0) :
    Function.Periodic (cumulative g) L := by
  obtain ⟨f, hf, he, hb, hp⟩ := divisorResidueSpan_lift hg
  exact cumulative_periodic_of_zero_period g L hp hz
theorem legalPrimitive_pullback (M L : ℕ) (hM : 0 < M) (_hL : 0 < L)
    (hML : M ∣ L) (R : Fin M → ℝ) (hR : IsLegalPrimitive M R) :
    IsLegalPrimitive L (R ∘ reduction M L hM) := by
  obtain ⟨g, hg, hz, h⟩ := hR
  have hp := legal_cumulative_periodic g M hg hz
  refine ⟨g, divisorResidueSpan_mono hML hg, ?_, ?_⟩
  · have he := hp.map_mod_nat L
    simpa [Nat.mod_eq_zero_of_dvd hML] using he.symm
  · intro b
    exact (h (reduction M L hM b)).trans (hp.map_mod_nat b.val)
theorem legalPrimitive_energy (L : ℕ) (hL : 0 < L) (R : Fin L → ℝ)
    (g : ℕ → ℝ) (hg : g ∈ divisorResidueSpan L) (hz : cumulative g L = 0)
    (hR : ∀ a : Fin L, R a = cumulative g a.val) :
    energy (residueWeight L) R = qConditionalMeanSquare g := by
  rw [QWeightedResidues.periodic_cumulative_energy g L hL
    (legal_cumulative_periodic g L hg hz)]
  unfold energy
  apply Finset.sum_congr rfl
  intro a _
  rw [hR a]
end RiemannResearch.RH.SquarefreeWeightedPrimitives
