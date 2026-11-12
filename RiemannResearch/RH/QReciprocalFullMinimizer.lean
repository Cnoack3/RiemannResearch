import RiemannResearch.RH.QReciprocalFiniteCost
import RiemannResearch.RH.QCanonicalMobiusCostRates
import RiemannResearch.RH.QReciprocalCofinalCost

/-!
# An explicit full-conductor regularized minimizer

Conductors 2 through H+1 are retained. The inverse of the complete regularized Gram matrix defines the optimizer. It improves every competitor in that span, including the boundary-corrected Mobius exact-head family. Cofinal and near-linear bounds imply RH, but remain open arithmetic providers.

Research agenda: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 9.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QReciprocalFullMinimizer
open ZetaTwoHilbert ZetaTwoProbability QReciprocalMetric QReciprocalCostEquivalence
open QReciprocalFiniteCost QMobiusExactHead
open RiemannResearch.Analysis.FiniteHilbertGram

def fullMinimizer (H : ℕ) (α : ℝ) : QHilbert :=
  minimizer (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) qOne α

def fullValue (H : ℕ) (α : ℝ) : ℝ :=
  ‖D qOne‖^2 -
    dotProduct (load (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) qOne)
      (coefficients (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) qOne α)

theorem fullMinimizer_legal (H : ℕ) (α : ℝ) :
    fullMinimizer H α ∈ QFullResidueProjection.legalSpan :=
  residue_minimizer_legal _ (QFullResidueProjection.conductor_gt_one H) qOne α

private theorem atom_mem (H d : ℕ) (hd : 0 < d) (hle : d ≤ H+1) :
    qResidue d ∈ synthesisSpan
      (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) := by
  by_cases hd1 : d = 1
  · rw [hd1, qResidue_one]
    exact Submodule.zero_mem _
  · apply Submodule.subset_span
    refine ⟨⟨d-2,by omega⟩,?_⟩
    change qResidue (d-2+2) = qResidue d
    congr 1
    omega

theorem exactHead_mem (H : ℕ) :
    exactHead H ∈ synthesisSpan
      (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) := by
  unfold exactHead
  apply Submodule.add_mem
  · apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro d hd
    have h := Finset.mem_Icc.mp hd
    exact Submodule.smul_mem _ _ (atom_mem H d h.1 (by omega))
  · exact Submodule.smul_mem _ _ (atom_mem H (H+1) (by omega) le_rfl)

theorem full_minimum_value (H : ℕ) (α : ℝ) (hα : 0 < α) :
    cost α qOne (fullMinimizer H α) = fullValue H α :=
  minimum_value _ (QResidueTriangular.qResidue_linearIndependent_injective _
    (QFullResidueProjection.conductor_gt_one H)
    (QFullResidueProjection.conductor_injective H)) qOne α hα

theorem fullValue_nonneg (H : ℕ) (α : ℝ) (hα : 0 < α) : 0 ≤ fullValue H α := by
  rw [← full_minimum_value H α hα]
  unfold cost
  positivity

theorem fullValue_le_exactHead (H : ℕ) (α : ℝ) (hα : 0 < α) :
    fullValue H α ≤ cost α qOne (exactHead H) := by
  rw [← full_minimum_value H α hα]
  exact minimizer_le _ (QResidueTriangular.qResidue_linearIndependent_injective _
    (QFullResidueProjection.conductor_gt_one H)
    (QFullResidueProjection.conductor_injective H)) qOne (exactHead H)
    (exactHead_mem H) α hα

theorem fullValue_source_bound (H : ℕ) (hH : 0 < H) :
    fullValue H ((H : ℝ)^2)⁻¹ ≤
      (4/zetaTwo)*((H : ℝ)^2)⁻¹*‖Pareto.canonicalMobiusHilbert H‖^2 := by
  exact (fullValue_le_exactHead H _ (by positivity)).trans
    (QCanonicalMobiusCost.balanced_cost_source_upper H hH)

theorem fullValue_explicit (H : ℕ) (hH : 0 < H) :
    fullValue H ((H : ℝ)^2)⁻¹ ≤ 16/(zetaTwo*(H : ℝ)) :=
  (fullValue_le_exactHead H _ (by positivity)).trans
    (QCanonicalMobiusCost.balanced_cost_explicit H hH)

open RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem fullValue_global_sqrt_log (c : ℝ) (hc : 0 < c)
    (hcE : c < Quantitative.MobiusContour.contourEndpoint) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, 0 < H →
      fullValue H ((H : ℝ)^2)⁻¹ ≤
        12/(zetaTwo*(H : ℝ)^2) + C/(H : ℝ)*Real.exp (-c*Real.sqrt (Real.log (H : ℝ))) := by
  obtain ⟨C,hC,h⟩ := QCanonicalMobiusCost.balanced_cost_global_sqrt_log c hc hcE
  exact ⟨C,hC,fun H hH => (fullValue_le_exactHead H _ (by positivity)).trans (h H hH)⟩

theorem riemannHypothesis_of_cofinal_fullValue
    (reg : ℕ → ℝ) (hr : ∀ H, 0 < reg H)
    (hr0 : Tendsto reg atTop (𝓝 0))
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ N, ∃ H, N ≤ H ∧ fullValue H (reg H) ≤ C*reg H) :
    RiemannHypothesis := by
  apply QReciprocalCofinalCost.riemannHypothesis_of_cofinal_cost reg hr hr0
    (fun H => fullMinimizer H (reg H)) (fun H => fullMinimizer_legal H (reg H)) C hC
  intro N
  obtain ⟨H,hH,hb⟩ := h N
  exact ⟨H,hH,by simpa only [full_minimum_value H (reg H) (hr H)] using hb⟩

open QReciprocalRegularizedCriterion

theorem riemannHypothesis_of_near_linear_fullValue
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      fullValue (QCanonicalMobiusCost.stage j) (regularizationScale j) ≤
        C*(regularizationScale j)^(1-η)) : RiemannHypothesis := by
  apply riemannHypothesis_of_near_linear_D_cost
    (fun j => fullMinimizer (QCanonicalMobiusCost.stage j) (regularizationScale j))
    (fun j => fullMinimizer_legal _ _)
  intro η hη
  obtain ⟨C,hC,hCj⟩ := h η hη
  refine ⟨C,hC,fun j => ?_⟩
  have hj := hCj j
  rw [← full_minimum_value _ _ (regularizationScale_pos j)] at hj
  simpa only [cost, map_sub, norm_sub_rev] using hj

end RiemannResearch.RH.QReciprocalFullMinimizer
