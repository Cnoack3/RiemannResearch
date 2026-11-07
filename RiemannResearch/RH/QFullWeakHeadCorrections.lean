/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.BoundedWeakInterpolation
import RiemannResearch.RH.QFullCrossedDistances
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullCofinalHarmonic
import RiemannResearch.RH.QParetoSquareRootEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace

/-!
# Full-conductor bounded-head correction criterion

Source: the user's weak-star compactness request and
CrossedDistanceLeanHandoff20261106.md, 6 November 2026.
The closed space below is the full-conductor legal closure. Uniform full-norm
bounds on the finite-head corrections remain explicit open provider hypotheses.
Banach--Alaoglu yields exact limiting corrections without assuming their strong
convergence or a vanishing complete correction-error sequence.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QFullWeakHeadCorrections
open ZetaTwoHilbert QFullResidueProjection QFullDisplacement
open QParetoIsometricTransport QFullCrossedDistances

/-- Conditional research reduction: uniformly bounded legal corrections for
every finite head give exact common-target corrections and zero displacement. -/
theorem displacement_eq_zero_of_bounded_head_corrections (C D : ℝ)
    (hh : ∀ N, ∃ h ∈ closure, ‖h‖ ≤ C ∧
      ∀ n < N, inversePhysical h n = rootDefect displacement n)
    (hk : ∀ N, ∃ k ∈ closure, ‖k‖ ≤ D ∧
      ∀ n < N, k n = rootDefect displacement n) : displacement = 0 := by
  obtain ⟨h, hmem, _hn, he⟩ :=
    (closure.bounded_lp_head_image_feasibility_iff C inversePhysical
      (rootDefect displacement)).mp hh
  obtain ⟨k, kmem, _kn, ke⟩ :=
    (closure.bounded_lp_head_image_feasibility_iff D (ContinuousLinearMap.id ℝ QHilbert)
      (rootDefect displacement)).mp hk
  have he' : rootDefect displacement - inversePhysical h = 0 :=
    sub_eq_zero.mpr he.symm
  have ke' : rootDefect displacement - k = 0 := sub_eq_zero.mpr ke.symm
  have ha : forwardDistance displacement = 0 := by
    have hle : forwardDistance displacement ≤ 0 := by
      simpa only [he', norm_zero] using
        forwardDistance_le_rootDefect_trial displacement h displacement_mem hmem
    exact le_antisymm hle Metric.infDist_nonneg
  have hb : inverseDistance displacement = 0 := by
    have hle : inverseDistance displacement ≤ 0 := by
      simpa only [ke', norm_zero, mul_zero] using
        inverseDistance_le_rootDefect_trial displacement k displacement_mem kmem
    exact le_antisymm hle Metric.infDist_nonneg
  apply displacement_eq_zero_of_budget_zero
  simp only [crossedBudget, ha, hb, mul_zero, add_zero]

/-- The missing content is the uniform full-norm bound across all finite heads. -/
theorem displacement_eq_zero_iff_bounded_head_corrections :
    displacement = 0 ↔ ∃ C D : ℝ,
      (∀ N, ∃ h ∈ closure, ‖h‖ ≤ C ∧
        ∀ n < N, inversePhysical h n = rootDefect displacement n) ∧
      (∀ N, ∃ k ∈ closure, ‖k‖ ≤ D ∧
        ∀ n < N, k n = rootDefect displacement n) := by
  constructor
  · intro hd
    refine ⟨0, 0, ?_, ?_⟩
    · intro N
      refine ⟨0, closure.zero_mem, by simp, ?_⟩
      intro n hn
      simp [hd]
    · intro N
      refine ⟨0, closure.zero_mem, by simp, ?_⟩
      intro n hn
      simp [hd]
  · rintro ⟨C, D, hh, hk⟩
    exact displacement_eq_zero_of_bounded_head_corrections C D hh hk

theorem riemannHypothesis_of_bounded_head_corrections (C D : ℝ)
    (hh : ∀ N, ∃ h ∈ closure, ‖h‖ ≤ C ∧
      ∀ n < N, inversePhysical h n = rootDefect displacement n)
    (hk : ∀ N, ∃ k ∈ closure, ‖k‖ ≤ D ∧
      ∀ n < N, k n = rootDefect displacement n) : RiemannHypothesis :=
  riemannHypothesis_of_displacement_eq_zero
    (displacement_eq_zero_of_bounded_head_corrections C D hh hk)

end RiemannResearch.RH.QFullWeakHeadCorrections
