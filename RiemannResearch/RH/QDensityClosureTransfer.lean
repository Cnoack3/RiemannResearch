import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QReciprocalFullDensity
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Lean.Elab.Tactic.Omega

/-!
# Full-conductor closure transfers and the remaining RH premise

Source: user-provided notation correction and RH audit, 12 November 2026.
All density statements use conductors k >= 2. The reciprocal and augmented
densities are unconditional. The unaugmented legal closure remains an input
to every RH implication. Density invariance is proved equivalent to totality,
rather than silently supplied as a consequence of change of measure.
-/

noncomputable section
namespace RiemannResearch.RH.QDensityClosureTransfer
open ZetaTwoHilbert ZetaTwoProbability QDensityMetric QReciprocalMetric
open QDensityMetricInverse QFullResidueProjection
local notation "R" => QShiftedReciprocal.B

theorem map_legalSpan (T : QHilbert →ₗ[ℝ] QHilbert) :
    legalSpan.map T = Submodule.span ℝ
      {f : QHilbert | ∃ k : ℕ, 2 ≤ k ∧ f = T (qResidue k)} := by
  unfold legalSpan
  rw [Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i + 2, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨qResidue k, ?_, rfl⟩
    exact ⟨k - 2, congrArg qResidue (Nat.sub_add_cancel hk)⟩

theorem full_D_map_dense :
    (legalSpan.map D.toLinearMap).topologicalClosure = ⊤ := by
  rw [map_legalSpan]
  exact QReciprocalFullDensity.fullReciprocalClosure_eq_top

/-- Full R-density follows from full D-density via the bounded inverse density. -/
theorem full_R_map_dense :
    (legalSpan.map (R).toLinearMap).topologicalClosure = ⊤ := by
  let K := (legalSpan.map (R).toLinearMap).topologicalClosure
  let J := K.comap inverse.toLinearMap
  have hJclosed : IsClosed (J : Set QHilbert) :=
    (Submodule.isClosed_topologicalClosure _).preimage inverse.continuous
  have hDJ : legalSpan.map D.toLinearMap ≤ J := by
    rintro _ ⟨f, hf, rfl⟩
    change inverse (D f) ∈ K
    rw [inverse_D]
    exact K.smul_mem _ (Submodule.le_topologicalClosure _ ⟨f, hf, rfl⟩)
  have hJ : J = ⊤ := by
    have h := (legalSpan.map D.toLinearMap).topologicalClosure_minimal hDJ hJclosed
    rw [full_D_map_dense] at h
    exact top_unique h
  apply top_unique
  intro f _
  have h : B f ∈ J := by rw [hJ]; trivial
  change inverse (B f) ∈ K at h
  simpa only [inverse_B] using h

/-- This is totality of the augmented family, with the entire Q norm. -/
theorem full_augmentedClosure_eq_top :
    (augmentedSpan {k : ℕ | 2 ≤ k}).topologicalClosure = ⊤ := by
  let K := (augmentedSpan {k : ℕ | 2 ≤ k}).topologicalClosure
  have hDK : Submodule.span ℝ
      {f : QHilbert | ∃ k : ℕ, 2 ≤ k ∧ f = D (qResidue k)} ≤ K := by
    apply Submodule.span_le.mpr
    rintro f ⟨k, hk, rfl⟩
    have hg : qResidue k ∈ K :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, hk, Or.inl rfl⟩)
    have hBg : B (qResidue k) ∈ K :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, hk, Or.inr rfl⟩)
    rw [D_eq_density]
    exact K.sub_mem (K.smul_mem _ hBg) hg
  have h := Submodule.topologicalClosure_minimal _ hDK
    (Submodule.isClosed_topologicalClosure _)
  rw [QReciprocalFullDensity.fullReciprocalClosure_eq_top] at h
  exact top_unique h

/-- The closure of the B-images is exactly B(V). -/
theorem densityClosure_eq_image :
    (legalSpan.map B.toLinearMap).topologicalClosure =
      closure.map B.toLinearMap :=
  (map_closure legalSpan).symm

theorem densityClosure_eq_top_iff :
    (legalSpan.map B.toLinearMap).topologicalClosure = ⊤ ↔ closure = ⊤ :=
  density_closure_eq_top_iff legalSpan

/-- Checking every density image lies in V is exactly as strong as totality. -/
theorem fullClosure_eq_top_iff_density_generators_mem :
    closure = ⊤ ↔ ∀ k : ℕ, 2 ≤ k → B (qResidue k) ∈ closure := by
  constructor
  · intro h k hk
    rw [h]
    trivial
  · intro h
    have hg (k : ℕ) (hk : 2 ≤ k) : qResidue k ∈ closure :=
      legalSpan.le_topologicalClosure (Submodule.subset_span
        ⟨k - 2, congrArg qResidue (Nat.sub_add_cancel hk)⟩)
    have hspan : augmentedSpan {k : ℕ | 2 ≤ k} ≤ QFullResidueProjection.closure := by
      apply Submodule.span_le.mpr
      rintro f ⟨k, hk, hf⟩
      rcases hf with rfl | rfl
      · exact hg k hk
      · exact h k hk
    have hh := Submodule.topologicalClosure_minimal _ hspan
      (Submodule.isClosed_topologicalClosure _)
    rw [full_augmentedClosure_eq_top] at hh
    exact top_unique hh

theorem fullClosure_eq_top_iff_density_invariant :
    closure = ⊤ ↔ ∀ f ∈ closure, B f ∈ closure := by
  constructor
  · intro h f hf
    rw [h]
    trivial
  · intro h
    apply fullClosure_eq_top_iff_density_generators_mem.mpr
    intro k hk
    apply h
    exact legalSpan.le_topologicalClosure (Submodule.subset_span
      ⟨k - 2, congrArg qResidue (Nat.sub_add_cancel hk)⟩)

/-- The target also changes under B; this is not membership of one in B(V). -/
theorem density_target_mem_iff :
    B qOne ∈ (legalSpan.map B.toLinearMap).topologicalClosure ↔ qOne ∈ closure :=
  mem_density_closure_iff legalSpan qOne

/-- Conditional research reduction: the unaugmented density remains open. -/
theorem riemannHypothesis_of_densityClosure_eq_top
    (h : (legalSpan.map B.toLinearMap).topologicalClosure = ⊤) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_qOne_mem_full_closure
  rw [densityClosure_eq_top_iff.mp h]
  trivial

/-- Conditional research reduction with the correctly transported target. -/
theorem riemannHypothesis_of_density_target
    (h : B qOne ∈ (legalSpan.map B.toLinearMap).topologicalClosure) :
    RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure (density_target_mem_iff.mp h)

/-- Conditional research reduction: preservation of V by B is not yet supplied. -/
theorem riemannHypothesis_of_density_invariant
    (h : ∀ f ∈ closure, B f ∈ closure) : RiemannHypothesis := by
  apply riemannHypothesis_of_qOne_mem_full_closure
  rw [fullClosure_eq_top_iff_density_invariant.mpr h]
  trivial

#print axioms full_R_map_dense
#print axioms full_augmentedClosure_eq_top
#print axioms fullClosure_eq_top_iff_density_invariant
#print axioms riemannHypothesis_of_density_target

end RiemannResearch.RH.QDensityClosureTransfer
