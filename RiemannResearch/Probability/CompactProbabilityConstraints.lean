import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Compact assembly of finite probability constraints

Source: the finite intersection property for compact spaces of probability
measures (Mathlib Prokhorov) and clopen evaluation continuity (Portmanteau).
Consumer: the arithmetic DPP spatial coupling finite-window reduction.
This assembles feasible constraints; it does not prove their feasibility.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Probability

/-- Evaluation on a clopen event is continuous for weak convergence. -/
theorem continuous_probabilityReal_clopen
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {E : Set Ω} (hE : IsClopen E) :
    Continuous (fun μ : ProbabilityMeasure Ω => (μ : Measure Ω).real E) := by
  have h : Continuous (fun μ : ProbabilityMeasure Ω => μ E) :=
    continuous_iff_continuousAt.mpr fun μ =>
      ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto tendsto_id hE
  exact NNReal.continuous_coe.comp h

/-- Compactness assembles finitely satisfiable clopen probability constraints.
No compatibility of the finite witnesses is required. -/
theorem exists_probabilityMeasure_clopen_constraints
    {Ω C : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [T2Space Ω] [BorelSpace Ω] [CompactSpace Ω] [HasOuterApproxClosed Ω]
    (E : C → Set Ω) (p : C → ℝ) (hE : ∀ c, IsClopen (E c))
    (hfinite : ∀ F : Finset C, ∃ μ : ProbabilityMeasure Ω,
      ∀ c ∈ F, (μ : Measure Ω).real (E c) = p c) :
    ∃ μ : ProbabilityMeasure Ω, ∀ c, (μ : Measure Ω).real (E c) = p c := by
  classical
  let A : C → Set (ProbabilityMeasure Ω) :=
    fun c => {μ | (μ : Measure Ω).real (E c) = p c}
  have hc : ∀ c, IsClosed (A c) := fun c =>
    isClosed_eq (continuous_probabilityReal_clopen (hE c)) continuous_const
  have hf : ∀ F : Finset C, (⋂ c ∈ F, A c).Nonempty := by
    intro F
    obtain ⟨μ, hμ⟩ := hfinite F
    exact ⟨μ, by simpa only [Set.mem_iInter, A, Set.mem_ofPred_eq] using hμ⟩
  obtain ⟨μ, hμ⟩ := CompactSpace.iInter_nonempty hc hf
  exact ⟨μ, by simpa only [Set.mem_iInter, A, Set.mem_ofPred_eq] using hμ⟩

end RiemannResearch.Probability
