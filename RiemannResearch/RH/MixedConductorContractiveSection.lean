import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.ThresholdHilbertDilation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Contractive sections of the Pareto legal mean

The split mean on the legal space has a bounded section. Its orthogonal section
has the least possible operator norm. A section of norm at most one exists
exactly when the screened line equals the ambient constant line.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

instance legalClosedSpace_completeSpace : CompleteSpace closedSpace :=
  (show IsClosed (closedSpace : Set ThresholdHilbert) from
    (Submodule.span ℝ (Set.range residueAtom)).isClosed_topologicalClosure).completeSpace_coe

private theorem meanSection_norm_at_one (s : ℝ →L[ℝ] closedSpace) :
    ‖s‖ = ‖(s 1 : ThresholdHilbert)‖ := by
  change ‖s‖ = ‖s 1‖
  apply le_antisymm
  · apply s.opNorm_le_bound (norm_nonneg _)
    intro t
    have ht : s t = t • s 1 := by simpa using s.map_smul t (1 : ℝ)
    rw [ht, norm_smul, mul_comm]
  · simpa using s.le_opNorm (1 : ℝ)

private theorem meanSection_mean_one {s : ℝ →L[ℝ] closedSpace}
    (hs : legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ) :
    inner ℝ (s 1 : ThresholdHilbert) hilbertOne = 1 :=
  congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) hs

/-- The excess squared norm of a section is the squared norm of its mixed component. -/
theorem legalMeanSection_norm_sq (s : ℝ →L[ℝ] closedSpace)
    (hs : legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ) :
    ‖s‖ ^ 2 = ‖normalizedScreenedTwo‖ ^ 2 +
      ‖(s 1 : ThresholdHilbert) - normalizedScreenedTwo‖ ^ 2 := by
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  have hm : (s 1 : ThresholdHilbert) - normalizedScreenedTwo ∈ mixedClosure := by
    apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
    refine ⟨closedSpace.sub_mem (s 1).property hu.1, ?_⟩
    rw [inner_sub_left, meanSection_mean_one hs, normalizedScreenedTwo_mean, sub_self]
  have ho := (mixedClosure.mem_orthogonal normalizedScreenedTwo).mp hu.2 _ hm
  rw [inner_sub_left, real_inner_self_eq_norm_sq, sub_eq_zero] at ho
  rw [meanSection_norm_at_one, norm_sub_sq_real, ho]
  ring

/-- Splitting the legal mean by a contraction is equivalent to equality of the two
ambient lines. The usual bounded splitting is supplied by screenedMeanSection. -/
theorem screenedPrimeClosure_eq_constantLine_iff_contractive_section :
    screenedPrimeClosure = Submodule.span ℝ {hilbertOne} ↔
      ∃ s : ℝ →L[ℝ] closedSpace,
        legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ 1 := by
  constructor
  · intro h
    have hW : hilbertOne ∈ screenedPrimeClosure := by
      rw [h]
      exact Submodule.subset_span (Set.mem_singleton _)
    have hu := one_mem_closedSpace_iff_normalizedScreenedTwo.mp
      (screenedPrimeClosure_le_closedSpace hW)
    refine ⟨screenedMeanSection, legalPacketMean_comp_screenedMeanSection, ?_⟩
    rw [meanSection_norm_at_one]
    change ‖(1 : ℝ) • normalizedScreenedTwo‖ ≤ 1
    rw [one_smul, hu]
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  · rintro ⟨s, hs, hbound⟩
    rw [meanSection_norm_at_one] at hbound
    have herr := norm_sub_sq_real (s 1 : ThresholdHilbert) hilbertOne
    rw [meanSection_mean_one hs, hilbertOne_norm_sq] at herr
    have hsquare := mul_self_le_mul_self (norm_nonneg (s 1 : ThresholdHilbert)) hbound
    have hzero : ‖(s 1 : ThresholdHilbert) - hilbertOne‖ ^ 2 = 0 :=
      le_antisymm (by nlinarith only [herr, hsquare]) (sq_nonneg _)
    rw [pow_two, mul_eq_zero, or_self] at hzero
    have he := sub_eq_zero.mp (norm_eq_zero.mp hzero)
    have hV : hilbertOne ∈ closedSpace := he ▸ (s 1).property
    rw [screenedPrimeClosure_eq_span_two, one_mem_closedSpace_iff_normalizedScreenedTwo.mp hV]

/-- The adjoint of the quotient mean is its orthogonal section scaled by the
captured constant energy. -/
theorem legalPacketMean_adjoint_eq_scaled_section :
    legalPacketMean.adjoint = (1 - limitEnergy) • screenedMeanSection := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro t v
  change inner ℝ ((1 - limitEnergy) • (t • normalizedScreenedTwo)) (v : ThresholdHilbert) =
    inner ℝ t (inner ℝ (v : ThresholdHilbert) hilbertOne)
  have h := (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ v.property
  rw [limitResidual, inner_sub_right, sub_eq_zero] at h
  rw [smul_comm (1 - limitEnergy) t, ← limitProjection_eq_scaled_screenedTwo,
    real_inner_smul_left, real_inner_comm (v : ThresholdHilbert) limitProjection, ← h]
  simp [Real.inner_apply, mul_comm]

/-- The coisometry equation for the legal mean has an exact scalar defect. -/
theorem legalPacketMean_comp_adjoint :
    legalPacketMean.comp legalPacketMean.adjoint =
      (1 - limitEnergy) • ContinuousLinearMap.id ℝ ℝ := by
  rw [legalPacketMean_adjoint_eq_scaled_section]
  apply ContinuousLinearMap.ext
  intro t
  change legalPacketMean ((1 - limitEnergy) • screenedMeanSection t) = (1 - limitEnergy) • t
  rw [map_smul]
  exact congrArg (fun r : ℝ => (1 - limitEnergy) • r)
    (congrArg (fun f : ℝ →L[ℝ] ℝ => f t) legalPacketMean_comp_screenedMeanSection)

/-- The legal mean is a coisometry exactly when the screened line is the constant line. -/
theorem screenedPrimeClosure_eq_constantLine_iff_coisometry :
    screenedPrimeClosure = Submodule.span ℝ {hilbertOne} ↔
      legalPacketMean.comp legalPacketMean.adjoint = ContinuousLinearMap.id ℝ ℝ := by
  rw [legalPacketMean_comp_adjoint]
  constructor
  · intro h
    have hW : hilbertOne ∈ screenedPrimeClosure := by
      rw [h]
      exact Submodule.subset_span (Set.mem_singleton _)
    rw [limitEnergy_zero_iff_mem.mpr (screenedPrimeClosure_le_closedSpace hW),
      sub_zero, one_smul]
  · intro h
    have ht := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) h
    change (1 - limitEnergy) * 1 = (1 : ℝ) at ht
    have hE : limitEnergy = 0 := by linarith
    rw [screenedPrimeClosure_eq_span_two, one_mem_closedSpace_iff_normalizedScreenedTwo.mp
      (limitEnergy_zero_iff_mem.mp hE)]

/-- Integer dilation preserves the splitting identity while multiplying the squared norm
of the orthogonal section by the dilation factor. -/
theorem exists_legalMeanSection_norm_sq_dilation (d : ℕ) (hd : 0 < d) :
    ∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧
        ‖s‖ ^ 2 = (d : ℝ) * ‖normalizedScreenedTwo‖ ^ 2 := by
  let x : closedSpace := ⟨hilbertDilation d hd normalizedScreenedTwo,
    closedSpace_dilation
      (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure)
      d hd⟩
  let s : ℝ →L[ℝ] closedSpace := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  refine ⟨s, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro t
    change inner ℝ (t • hilbertDilation d hd normalizedScreenedTwo) hilbertOne = t
    rw [real_inner_smul_left, hilbert_inner_one, hilbertDilation_mean, ← hilbert_inner_one,
      normalizedScreenedTwo_mean, mul_one]
  · rw [meanSection_norm_at_one]
    change ‖(1 : ℝ) • hilbertDilation d hd normalizedScreenedTwo‖ ^ 2 = _
    rw [one_smul, hilbertDilation_norm_sq]

end RiemannResearch.RH.Pareto.PrimePowerSchur
