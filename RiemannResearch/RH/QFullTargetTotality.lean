import RiemannResearch.RH.QDensityClosureTransfer
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QAnnihilatorDilationEscape
import RiemannResearch.RH.QReciprocalTargetLift
import RiemannResearch.RH.QReciprocalCostEquivalence
import RiemannResearch.RH.QFullResidueProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The constant target is equivalent to full residue totality

Source: Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis", Theorem 1 and Theorem 7,
https://arxiv.org/abs/math/0607733. This supports the statement and
integer-dilation proof strategy. The exact Q implementation uses the
existing floor-dilation and step-separation theorems.
The analytic RH-to-target implication is not assumed or postulated here.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QFullTargetTotality
open ZetaTwoHilbert QFullResidueProjection QFloorDilation

/-- Arithmetic floor dilation upgrades constant approximation to full totality. -/
theorem closure_eq_top_iff_one_mem : closure = ⊤ ↔ qOne ∈ closure := by
  constructor
  · intro h
    rw [h]
    trivial
  · intro h
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro u hu
    change u = 0
    by_contra hne
    obtain ⟨m, hm, hpair⟩ := QAnnihilatorDilationEscape.exists_nonzero_step_pairing u hne
    exact hpair (Submodule.inner_right_of_mem_orthogonal
      (floorDilation_mem_legalClosure m hm qOne h) hu)

/-- For this arithmetic space, density invariance is no stronger than target membership. -/
theorem one_mem_iff_density_invariant :
    qOne ∈ closure ↔ ∀ f ∈ closure, QDensityMetric.B f ∈ closure :=
  closure_eq_top_iff_one_mem.symm.trans
    QDensityClosureTransfer.fullClosure_eq_top_iff_density_invariant

theorem one_mem_iff_all_density_generators :
    qOne ∈ closure ↔ ∀ k : ℕ, 2 ≤ k → QDensityMetric.B (qResidue k) ∈ closure :=
  closure_eq_top_iff_one_mem.symm.trans
    QDensityClosureTransfer.fullClosure_eq_top_iff_density_generators_mem

/-- A bounded lift of just the constant already forces the entire legal closure to be H. -/
theorem closure_eq_top_iff_bounded_lift :
    closure = ⊤ ↔ ∃ C : ℝ, ∃ F : ℕ → QHilbert,
      (∀ j, F j ∈ closure) ∧ (∀ j, ‖F j‖ ≤ C) ∧
        Tendsto (fun j => QReciprocalMetric.D (F j)) atTop
          (𝓝 (QReciprocalMetric.D qOne)) :=
  closure_eq_top_iff_one_mem.trans
    (QReciprocalTargetLift.bounded_D_lift_iff_mem closure qOne).symm

/-- Exact equivalence for any prescribed positive regularization schedule tending to zero. -/
theorem closure_eq_top_iff_regularized_cost (reg : ℕ → ℝ)
    (hr : ∀ j, 0 < reg j) (hrlim : Tendsto reg atTop (𝓝 0)) :
    closure = ⊤ ↔ ∃ C : ℝ, 0 ≤ C ∧ ∃ F : ℕ → QHilbert,
      (∀ j, F j ∈ legalSpan) ∧
      (∀ j, QReciprocalCostEquivalence.cost (reg j) qOne (F j) ≤ C * reg j) :=
  closure_eq_top_iff_one_mem.trans
    (QReciprocalCostEquivalence.mem_closure_iff_regularized_cost legalSpan qOne reg hr hrlim)

#print axioms closure_eq_top_iff_one_mem
#print axioms closure_eq_top_iff_regularized_cost
end RiemannResearch.RH.QFullTargetTotality
