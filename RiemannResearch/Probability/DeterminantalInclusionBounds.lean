import RiemannResearch.Probability.DeterminantalConditioning
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith

/-!
# Finite determinantal inclusion lower bounds

Source: user-provided union-bound argument, 24 October 2026.
The DPP inclusion convention follows Kulesza--Taskar,
https://arxiv.org/abs/1207.6083, Section 2. The proof is the ordinary
union bound for the vacancy events; it needs no independence.
The actual Q-Hilbert consumer is RH/QRamanujanDPPTraceBounds.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace RiemannResearch.Probability.DPP
variable {ι α Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}
theorem IsDPP.inclusion_lower_bound (h : IsDPP μ X K) (e : ι → α) :
    1 - ∑ i, (1 - K (e i) (e i)) ≤ μ.real {ω | ∀ i, e i ∈ X ω} := by
  have hm : MeasurableSet {ω | ∀ i, e i ∈ X ω} := by
    convert MeasurableSet.iInter (fun i => h.measurable_occupancy (e i)) using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  have hc : {ω | ∀ i, e i ∈ X ω}ᶜ = ⋃ i, {ω | e i ∉ X ω} := by
    ext ω
    simp
  have hu := measureReal_iUnion_fintype_le (μ := μ) (fun i => {ω | e i ∉ X ω})
  rw [← hc, probReal_compl_eq_one_sub hm] at hu
  simp_rw [h.vacancy] at hu
  linarith
theorem IsDPP.det_lower_bound_trace_defect (h : IsDPP μ X K) (e : ι ↪ α) :
    1 - (1 - Matrix.of (fun i j => K (e i) (e j))).trace ≤
      (Matrix.of (fun i j => K (e i) (e j))).det := by
  have hh := h.inclusion_lower_bound e
  rw [h.correlation_fintype e] at hh
  simpa only [Matrix.trace, Matrix.diag, Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.of_apply] using hh
end RiemannResearch.Probability.DPP
