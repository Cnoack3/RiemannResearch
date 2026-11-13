import RiemannResearch.RH.QCompactPhysicalBounds
import RiemannResearch.RH.QFullCRTDisplacement
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.NumberTheory.ProfiniteGeneralizedCRT
import Mathlib.Tactic.Push

/-!
# Actual displacement on the full profinite inverse limit

Source: the user's correction from the prime projection d_W to the actual
matched Q/P displacement d, 2026-11-12. We apply the repository's checked
bounded-displacement rigidity separately to its full-conductor and squarefree
displacements. Neither is replaced by a prime projection.

A continuous extension to the full profinite integers exists if and only if
the corresponding actual displacement is zero. More strongly, a finite
uniform error from any compact continuous trace already forces zero.
For a nonzero displacement every such uniform error is unbounded.

These are exact rigidity theorems and conditional RH reductions.
They do not prove existence of an extension or vanishing of either displacement.
The inverse-limit space is GeneralizedCRT.ProfiniteInt, which retains
all positive moduli, including every prime-power depth.
-/

noncomputable section
namespace RiemannResearch.RH.QDisplacementProfiniteContinuity
open ZetaTwoHilbert QCompactPhysicalBounds
open RiemannResearch.NumberTheory.GeneralizedCRT

/-- Continuous realization on the full inverse limit, retaining every prime-power depth. -/
def HasContinuousProfiniteExtension (f : QHilbert) : Prop :=
  ∃ F : C(ProfiniteInt, ℝ), ∀ n : ℕ, 1 ≤ n →
    F (n : ProfiniteInt) = qSequence f n

namespace Full
open QFullDisplacement

theorem zero_of_compact_bounded_error
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ι : ℕ → X) (F : C(X, ℝ)) (C : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → |qSequence displacement n - F (ι n)| ≤ C) :
    displacement = 0 := by
  obtain ⟨K, hK⟩ := physically_bounded_of_compact_error ι displacement F C h
  exact displacement_eq_zero_of_qResidual_eq_zero
    (QFullCRTDisplacement.residual_zero_of_physically_bounded K hK)

/-- Exact equivalence; existence of the extension remains an open arithmetic obligation. -/
theorem profinite_extension_iff_zero :
    HasContinuousProfiniteExtension displacement ↔ displacement = 0 := by
  constructor
  · rintro ⟨F, hF⟩
    apply zero_of_compact_bounded_error (fun n : ℕ => (n : ProfiniteInt)) F 0
    intro n hn
    simp only [← hF n hn, sub_self, abs_zero, le_refl]
  · intro hd
    refine ⟨0, ?_⟩
    intro n hn
    rw [hd]
    simp only [ContinuousMap.zero_apply, ← qEvalCLM_apply, map_zero]

theorem rh_of_profinite_extension
    (h : HasContinuousProfiniteExtension displacement) : RiemannHypothesis := by
  have hd := profinite_extension_iff_zero.mp h
  have hb : ∀ n : ℕ, |qSequence displacement n| ≤ 0 := by
    intro n
    simp only [hd, ← qEvalCLM_apply, map_zero, abs_zero, le_refl]
  exact QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (qResidual_eq_zero_iff.mp
      (QFullCRTDisplacement.residual_zero_of_physically_bounded 0 hb))

/-- A nonzero actual displacement has infinite uniform error against every compact
continuous trace, even though its finite projections converge in Q norm. -/
theorem unbounded_error_of_ne_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ι : ℕ → X) (hd : displacement ≠ 0) (F : C(X, ℝ)) (C : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ C < |qSequence displacement n - F (ι n)| := by
  by_contra h
  push Not at h
  exact hd (zero_of_compact_bounded_error ι F C h)

end Full

namespace Squarefree
open QSquarefreeDisplacementRigidity

theorem zero_of_compact_bounded_error
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ι : ℕ → X) (F : C(X, ℝ)) (C : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → |qSequence displacement n - F (ι n)| ≤ C) :
    displacement = 0 := by
  obtain ⟨K, hK⟩ := physically_bounded_of_compact_error ι displacement F C h
  exact displacement_eq_zero_of_residual_eq_zero
    (residual_eq_zero_of_displacement_physically_bounded K hK)

/-- The squarefree displacement has the same rigidity on the full profinite limit. -/
theorem profinite_extension_iff_zero :
    HasContinuousProfiniteExtension displacement ↔ displacement = 0 := by
  constructor
  · rintro ⟨F, hF⟩
    apply zero_of_compact_bounded_error (fun n : ℕ => (n : ProfiniteInt)) F 0
    intro n hn
    simp only [← hF n hn, sub_self, abs_zero, le_refl]
  · intro hd
    refine ⟨0, ?_⟩
    intro n hn
    rw [hd]
    simp only [ContinuousMap.zero_apply, ← qEvalCLM_apply, map_zero]

theorem rh_of_profinite_extension
    (h : HasContinuousProfiniteExtension displacement) : RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_bounded 0
  intro n
  simp only [profinite_extension_iff_zero.mp h, ← qEvalCLM_apply, map_zero,
    abs_zero, le_refl]

theorem unbounded_error_of_ne_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ι : ℕ → X) (hd : displacement ≠ 0) (F : C(X, ℝ)) (C : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ C < |qSequence displacement n - F (ι n)| := by
  by_contra h
  push Not at h
  exact hd (zero_of_compact_bounded_error ι F C h)

end Squarefree
end RiemannResearch.RH.QDisplacementProfiniteContinuity
