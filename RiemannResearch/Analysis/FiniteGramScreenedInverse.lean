/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramScreenedCapacity
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact inverse-source coefficients after screening a finite block

Source: user-provided primorial prime-packet research agenda, 16 October 2026,
Section 7. The general screened representer identity supplies the proof
strategy. This module retains both coefficient blocks and the full signed
correction to the old block. It imposes no capacity-growth hypothesis.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramCapacity
noncomputable section
open FiniteHilbertGram FiniteHilbertConstraints

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem synthesis_sum_block (u : ι → H) (w : κ → H)
    (a : ι → ℝ) (c : κ → ℝ) :
    Fintype.linearCombination ℝ (Sum.elim u w) (Sum.elim a c) =
      Fintype.linearCombination ℝ u a + Fintype.linearCombination ℝ w c := by
  simp only [Fintype.linearCombination_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]

private theorem synthesis_screened_block {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (c : κ → ℝ) :
    Fintype.linearCombination ℝ (screened hu w) c =
      Fintype.linearCombination ℝ w c -
        Fintype.linearCombination ℝ u (∑ j, c j • inverseCoeff hu (w j)) := by
  change (∑ j, c j • (w j - Fintype.linearCombination ℝ u (inverseCoeff hu (w j)))) = _
  rw [map_sum]
  simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
  rfl

/-- The exact block inverse action, including the correction to every old coefficient. -/
theorem inverseSource_screened_sum {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (hs : LinearIndependent ℝ (screened hu w))
    (hall : LinearIndependent ℝ (Sum.elim u w)) (b : ι → ℝ) (d : κ → ℝ) :
    inverseSource hall (Sum.elim b d) =
      Sum.elim
        (inverseSource hu b -
          ∑ j, inverseSource hs (screenedSource hu w b d) j • inverseCoeff hu (w j))
        (inverseSource hs (screenedSource hu w b d)) := by
  apply hall.fintypeLinearCombination_injective
  change minimumVector hall (Sum.elim b d) = _
  rw [minimumVector_screened_sum hu w hs hall b d, synthesis_sum_block, map_sub]
  change Fintype.linearCombination ℝ u (inverseSource hu b) +
      Fintype.linearCombination ℝ (screened hu w)
        (inverseSource hs (screenedSource hu w b d)) = _
  rw [synthesis_screened_block]
  abel

end
end RiemannResearch.Analysis.FiniteGramCapacity
