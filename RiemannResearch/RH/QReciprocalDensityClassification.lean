import RiemannResearch.RH.QReciprocalFullDensity
import RiemannResearch.RH.QReciprocalSpanObstruction

/-!
# Unconditional classification of the restricted reciprocal spans

Combines the full-conductor density theorem with the exact two-site
obstruction and the squarefree finite sieve. All conclusions concern
physical sequences, so the P/Q statements agree despite different
orthogonal projections. No RH hypothesis is used.
-/

noncomputable section
namespace RiemannResearch.RH.QReciprocalDensityClassification
open ZetaTwoHilbert QReciprocalMetric QReciprocalSpanObstruction
open QParetoEquivalence ZetaTwoParetoTransfer

/-- Omitting conductor two leaves precisely one continuous coordinate constraint. -/
theorem strict_reciprocalClosure_eq_ker :
    (reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure = twoSite.ker := by
  apply strict_reciprocalClosure_eq_twoSite_ker
  simpa only [reciprocalSpan, Set.mem_setOf_eq] using
    QReciprocalFullDensity.fullReciprocalClosure_eq_top

theorem strict_reciprocalClosure_mem_iff (f : QHilbert) :
    f ∈ (reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure ↔
      qSequence f 1 = qSequence f 2 := by
  rw [strict_reciprocalClosure_eq_ker]
  change twoSite f = 0 ↔ _
  rw [twoSite_apply, sub_eq_zero]

theorem pareto_strict_reciprocalClosure_mem_iff (f : QHilbert) :
    toPareto f ∈ ((reciprocalSpan {k : ℕ | 2 < k}).map
      paretoEquiv.toLinearMap).topologicalClosure ↔
      qSequence f 1 = qSequence f 2 := by
  rw [pareto_reciprocalClosure_mem_iff, strict_reciprocalClosure_mem_iff]

/-- Squarefree smoothing reaches the correct smoothed RH target unconditionally. -/
theorem D_one_mem_squarefree_reciprocalClosure :
    D qOne ∈ (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure := by
  apply QReciprocalFullDensity.D_one_mem_of_squarefree_residues
    _ (Submodule.isClosed_topologicalClosure _) one_mem_squarefree_reciprocalClosure
  intro k hk hs
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, ⟨hk, hs⟩, rfl⟩)

theorem pareto_D_one_mem_squarefree_reciprocalClosure :
    toPareto (D qOne) ∈ ((reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).map
      paretoEquiv.toLinearMap).topologicalClosure := by
  exact (pareto_reciprocalClosure_mem_iff _ _).mpr D_one_mem_squarefree_reciprocalClosure

end RiemannResearch.RH.QReciprocalDensityClassification
