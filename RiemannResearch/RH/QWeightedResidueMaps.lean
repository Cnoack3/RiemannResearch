/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QWeightedResidues
import RiemannResearch.Analysis.FiniteWeightedRefinement
/-!
# Arithmetic weighted residue maps

Source: user's weighted-CRT manuscript, 1 November 2026, weighted Hilbert
maps section. All weights are the exact Q primitive pushforwards.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QWeightedResidueMaps
open QWeightedResidues RiemannResearch.Analysis.FiniteWeightedRefinement
open RiemannResearch.Analysis.FiniteWeightedPushforward
def reduction (M L : ℕ) (hM : 0 < M) (b : Fin L) : Fin M :=
  ⟨b.val % M, Nat.mod_lt _ hM⟩
theorem pushed_residueWeight (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (hML : M ∣ L) :
    pushWeight (residueWeight L) (reduction M L hM) = residueWeight M := by
  classical
  funext a
  rw [pushWeight, tsum_fintype, residueWeight_refinement M L hM hL hML a]
  apply Finset.sum_congr rfl
  intro b _
  have he : reduction M L hM b = a ↔ b.val % M = a.val := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      exact Fin.ext h
  simp only [he]
theorem residue_pullback_energy (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (hML : M ∣ L) (f : Fin M → ℝ) :
    energy (residueWeight L) (f ∘ reduction M L hM) =
      energy (residueWeight M) f := by
  rw [pullback_energy, pushed_residueWeight M L hM hL hML]
open QWeightedResidues RiemannResearch.Analysis.FiniteWeightedRefinement
open RiemannResearch.Analysis.FiniteWeightedPushforward
def residueAverage (M L : ℕ) (hM : 0 < M) (F : Fin L → ℝ) : Fin M → ℝ :=
  average (residueWeight L) (reduction M L hM) F
theorem residue_adjoint_identity (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (hML : M ∣ L) (f : Fin M → ℝ) (F : Fin L → ℝ) :
    pairing (residueWeight L) (f ∘ reduction M L hM) F =
      pairing (residueWeight M) f (residueAverage M L hM F) := by
  have hm (a : Fin M) : pushWeight (residueWeight L) (reduction M L hM) a ≠ 0 := by
    rw [pushed_residueWeight M L hM hL hML]
    exact ne_of_gt (residueWeight_pos M hM a)
  simpa only [pushed_residueWeight M L hM hL hML, residueAverage] using
    adjoint_identity (residueWeight L) (reduction M L hM) hm f F
theorem residue_average_pullback (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (hML : M ∣ L) (f : Fin M → ℝ) :
    residueAverage M L hM (f ∘ reduction M L hM) = f := by
  funext a
  apply average_pullback
  intro a
  rw [pushed_residueWeight M L hM hL hML]
  exact ne_of_gt (residueWeight_pos M hM a)
end RiemannResearch.RH.QWeightedResidueMaps
