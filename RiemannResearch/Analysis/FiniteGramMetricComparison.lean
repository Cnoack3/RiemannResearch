/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramCapacity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Inverse-Gram comparison from a complete Gram-energy comparison

Source: the standard dual variational principle, used for the user's
Pareto-to-Q transfer, 15 October 2026. The proof uses the exact capacity
completion and the entire signed Hilbert synthesis norm. Its RH consumer
is `RH/QParetoGramComparison`.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramCapacity
open FiniteHilbertGram FiniteHilbertConstraints
variable {ι H K : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Comparison reverses on the inverse Gram, for every right-hand side. -/
theorem capacity_le_mul_of_energy_le {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ c : ι → ℝ, ‖Fintype.linearCombination ℝ v c‖ ^ 2 ≤
      C * ‖Fintype.linearCombination ℝ w c‖ ^ 2)
    (b : ι → ℝ) :
    capacity hw b ≤ C * capacity hv b := by
  let c := inverseSource hw b
  have hnorm : ‖Fintype.linearCombination ℝ w c‖ ^ 2 = capacity hw b :=
    (capacity_eq_norm_sq hw b).symm
  have hsrc := source_sq_le_capacity_mul_energy hv b c
  change (capacity hw b) ^ 2 ≤
    capacity hv b * ‖Fintype.linearCombination ℝ v c‖ ^ 2 at hsrc
  have he := henergy c
  rw [hnorm] at he
  have hh := hsrc.trans (mul_le_mul_of_nonneg_left he (capacity_nonneg hv b))
  by_cases hz : capacity hw b = 0
  · rw [hz]
    exact mul_nonneg hC (capacity_nonneg hv b)
  · have hp : 0 < capacity hw b := lt_of_le_of_ne (capacity_nonneg hw b) (Ne.symm hz)
    by_contra hnot
    have hlt : C * capacity hv b < capacity hw b := lt_of_not_ge hnot
    have hprod := mul_pos (sub_pos.mpr hlt) hp
    nlinarith only [hprod, hh]

end RiemannResearch.Analysis.FiniteGramCapacity
