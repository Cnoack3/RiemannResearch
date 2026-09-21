/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteGramCapacity
/-!
# Finite Gram capacity under translation by Hilbert observations

Source: continuation of the user-provided Pareto capacity handoff
(2026-09-21), for the source-translation strategy. These general identities
retain the exact signed mixed pairing. The RH application is in
ParetoCoprimeDefectVariational.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
namespace RiemannResearch.Analysis.FiniteGramCapacity
variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem minimumVector_sub_observed {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (z : H) :
    minimumVector hv (b - cross v z) =
      minimumVector hv b - minimumVector hv (cross v z) := by
  simp only [minimumVector, map_sub]
theorem capacity_sub_observed_exact {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (z : H) :
    capacity hv (b - cross v z) =
      capacity hv b - 2 * inner ℝ (minimumVector hv b) z +
        capacity hv (cross v z) := by
  have hpair : inner ℝ (minimumVector hv b) (minimumVector hv (cross v z)) =
      inner ℝ (minimumVector hv b) z := by
    unfold minimumVector
    rw [inner_synthesis_left, inner_synthesis_left]
    apply Finset.sum_congr rfl
    intro i _
    change _ * inner ℝ (v i) (minimumVector hv (cross v z)) = _
    rw [minimumVector_observation]
    rfl
  rw [capacity_eq_norm_sq, minimumVector_sub_observed, norm_sub_sq_real,
    hpair, ← capacity_eq_norm_sq, ← capacity_eq_norm_sq]
theorem capacity_sub_observed_le {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (z : H) :
    capacity hv (b - cross v z) ≤ 2 * capacity hv b + 2 * ‖z‖^2 := by
  have hp := minimumVector_minimizes hv (cross v z) z (fun _ => rfl)
  have hnorm := sq_nonneg ‖minimumVector hv b + minimumVector hv (cross v z)‖
  rw [norm_add_sq_real] at hnorm
  rw [capacity_eq_norm_sq, minimumVector_sub_observed]
  rw [capacity_eq_norm_sq, norm_sub_sq_real]
  nlinarith
theorem capacity_le_sub_observed {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (z : H) :
    capacity hv b ≤ 2 * capacity hv (b - cross v z) + 2 * ‖z‖^2 := by
  have h := capacity_sub_observed_le hv (b - cross v z) (-z)
  have he : b - cross v z - cross v (-z) = b := by
    funext i
    simp [cross]
  simpa only [he, norm_neg] using h
end RiemannResearch.Analysis.FiniteGramCapacity
