import RiemannResearch.RH.CenteredMeanLongExact
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Quotient topology and orthogonal models for the ambient mean snake

Throughout this file both complements and the centering range are formed in the
ambient Pareto Hilbert space. The quotient equivalence and the last scalar
section carry the quotient topologies from the two rows of the mean diagram.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization

/-- The change of quotient coordinates and its inverse are continuous. -/
def boundaryTargetContinuousEquivLegalQuotient :
    BoundaryTarget ≃L[ℝ] (ThresholdHilbert ⧸ closedSpace) where
  __ := boundaryTargetEquivLegalQuotient
  continuous_toFun := by
    apply mixedInMeanZero.isQuotientMap_mkQL.continuous_iff.mpr
    exact closedSpace.mkQL.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply closedSpace.isQuotientMap_mkQL.continuous_iff.mpr
    change Continuous (fun x : ThresholdHilbert =>
      boundaryTargetEquivLegalQuotient.symm (closedSpace.mkQ x))
    simp only [boundaryTargetEquivLegalQuotient_symm_mk]
    have hr : Continuous meanZeroRepresentative :=
      (continuous_id.sub (hilbertMeanContinuous.continuous.smul continuous_const)).subtype_mk _
    exact mixedInMeanZero.mkQL.continuous.comp hr

/-- Decomposing the input into its mixed and screened components computes its centered image. -/
theorem centerLegal_decomposition (v : closedSpace) :
    centerLegal v = (legalMixedRetraction v : ThresholdHilbert) +
      legalPacketMean v • (defect : ThresholdHilbert) := by
  change (v : ThresholdHilbert) - hilbertMeanContinuous v.val • hilbertOne =
    ((v : ThresholdHilbert) - legalPacketMean v • normalizedScreenedTwo) +
      legalPacketMean v • (normalizedScreenedTwo - hilbertOne)
  have hm : hilbertMeanContinuous v.val = legalPacketMean v := by
    change inner ℝ hilbertOne v.val = inner ℝ v.val hilbertOne
    exact real_inner_comm _ _
  rw [hm, smul_sub]
  abel

/-- The range of the middle vertical arrow in the snake diagram. -/
theorem centerLegal_range : LinearMap.range centerLegal.toLinearMap =
    mixedClosure ⊔ Submodule.span ℝ {(defect : ThresholdHilbert)} := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change centerLegal v ∈ _
    rw [centerLegal_decomposition]
    exact Submodule.add_mem_sup (legalMixedRetraction v).property
      (Submodule.mem_span_singleton.mpr ⟨_, rfl⟩)
  · apply sup_le
    · intro m hm
      refine ⟨legalMixedInclusion ⟨m, hm⟩, ?_⟩
      change center m = m
      rw [center_apply, show hilbertMeanContinuous m = 0 from
        (mixedInclusion ⟨m, hm⟩).property, zero_smul, sub_zero]
    · apply Submodule.span_le.mpr
      rintro _ (rfl : _ = (defect : ThresholdHilbert))
      refine ⟨screenedMeanSection 1, ?_⟩
      change center ((1 : ℝ) • normalizedScreenedTwo) = normalizedScreenedTwo - hilbertOne
      rw [one_smul, center_apply, show hilbertMeanContinuous normalizedScreenedTwo = 1 from
        (real_inner_comm _ _).trans normalizedScreenedTwo_mean, one_smul]

private theorem defectLine_le_mixed_orthogonal :
    Submodule.span ℝ {(defect : ThresholdHilbert)} ≤ mixedClosureᗮ :=
  Submodule.span_le.mpr (Set.singleton_subset_iff.mpr screenedTwo_sub_one_mem_orthogonals.2)

/-- The finite-dimensional summand is closed. Projection off the closed mixed
space then exhibits the whole range as the preimage of that line. -/
theorem centerLegal_range_isClosed : IsClosed (LinearMap.range centerLegal.toLinearMap :
    Set ThresholdHilbert) := by
  let D := Submodule.span ℝ {(defect : ThresholdHilbert)}
  have he : (LinearMap.range centerLegal.toLinearMap : Set ThresholdHilbert) =
      mixedClosureᗮ.starProjection ⁻¹' (D : Set ThresholdHilbert) := by
    rw [centerLegal_range]
    ext x
    change x ∈ mixedClosure ⊔ D ↔ mixedClosureᗮ.starProjection x ∈ D
    constructor
    · intro hx
      obtain ⟨m, hm, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
      have hm' : mixedClosureᗮ.starProjection m = 0 := by
        rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr hm,
          sub_self]
      simpa only [map_add, hm', zero_add,
        Submodule.starProjection_eq_self_iff.mpr (defectLine_le_mixed_orthogonal hd)] using hd
    · intro hx
      rw [Submodule.starProjection_orthogonal_val] at hx
      exact Submodule.mem_sup.mpr ⟨_, mixedClosure.starProjection_apply_mem x, _, hx, by abel⟩
  rw [he]
  have hd : IsClosed (D : Set ThresholdHilbert) := by
    have hfix : (D : Set ThresholdHilbert) = {x | D.starProjection x = x} := by
      ext x
      exact Submodule.starProjection_eq_self_iff.symm
    rw [hfix]
    exact isClosed_eq D.starProjection.continuous continuous_id
  exact hd.preimage mixedClosureᗮ.starProjection.continuous

/-- The last arrow of the snake sequence descends continuously to the cokernel. -/
def cokernelMeanContinuous : CenterCokernel →L[ℝ] ℝ where
  __ := cokernelMean
  cont := by
    apply (LinearMap.range centerLegal.toLinearMap).isQuotientMap_mkQL.continuous_iff.mpr
    exact hilbertMeanContinuous.continuous

/-- Ambient constants split the last arrow of the long exact sequence. -/
def cokernelMeanSection : ℝ →L[ℝ] CenterCokernel :=
  (LinearMap.range centerLegal.toLinearMap).mkQL.comp
    (ContinuousLinearMap.toSpanSingleton ℝ hilbertOne)

theorem cokernelMean_comp_section :
    cokernelMeanContinuous.comp cokernelMeanSection = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro t
  change hilbertMeanContinuous (t • hilbertOne) = t
  simp

/-- The common orthogonal summand in the three quotient models. -/
abbrev commonMeanOrthogonal := meanZero ⊓ closedSpaceᗮ

private theorem defectLine_orthogonal_inf :
    (Submodule.span ℝ {(defect : ThresholdHilbert)})ᗮ ⊓ (meanZero ⊓ mixedClosureᗮ) =
      commonMeanOrthogonal := by
  ext x
  have hu : closedSpaceᗮ = mixedClosureᗮ ⊓ (Submodule.span ℝ {normalizedScreenedTwo})ᗮ := by
    rw [Submodule.inf_orthogonal, legal_mixed_screened_orthogonal_sum.1]
  change x ∈ (Submodule.span ℝ {normalizedScreenedTwo - hilbertOne})ᗮ ⊓
    (meanZero ⊓ mixedClosureᗮ) ↔ x ∈ meanZero ⊓ closedSpaceᗮ
  rw [hu, meanZero_eq_orthogonal]
  simp only [Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right]
  change (inner ℝ (normalizedScreenedTwo - hilbertOne) x = 0 ∧
    inner ℝ hilbertOne x = 0 ∧ x ∈ mixedClosureᗮ) ↔
      inner ℝ hilbertOne x = 0 ∧ x ∈ mixedClosureᗮ ∧ inner ℝ normalizedScreenedTwo x = 0
  rw [inner_sub_left]
  exact ⟨fun ⟨h, hz, hm⟩ => ⟨hz, hm, by simpa [hz] using h⟩,
    fun ⟨hz, hm, hu'⟩ => ⟨by rw [hu', hz, sub_zero], hz, hm⟩⟩

/-- Orthogonal decomposition of the Hilbert model of the boundary target. -/
theorem defectLine_sup_common :
    Submodule.span ℝ {(defect : ThresholdHilbert)} ⊔ commonMeanOrthogonal =
      meanZero ⊓ mixedClosureᗮ := by
  rw [← defectLine_orthogonal_inf]
  apply Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
    ⟨defect.property, screenedTwo_sub_one_mem_orthogonals.2⟩)

/-- Orthogonal decomposition of the Hilbert model of the legal quotient. -/
theorem residualLine_sup_common :
    Submodule.span ℝ {limitResidual} ⊔ commonMeanOrthogonal = closedSpaceᗮ := by
  have he : (Submodule.span ℝ {limitResidual})ᗮ ⊓ closedSpaceᗮ = commonMeanOrthogonal := by
    ext x
    rw [show commonMeanOrthogonal = meanZero ⊓ closedSpaceᗮ from rfl, meanZero_eq_orthogonal]
    simp only [Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right]
    have h (hx : x ∈ closedSpaceᗮ) : inner ℝ limitResidual x = inner ℝ hilbertOne x := by
      change inner ℝ (hilbertOne - limitProjection) x = _
      rw [inner_sub_left, show inner ℝ limitProjection x = 0 from
        hx limitProjection (closedSpace.starProjection_apply_mem _), sub_zero]
    exact ⟨fun ⟨ha, hx⟩ => ⟨(h hx).symm.trans ha, hx⟩,
      fun ⟨hz, hx⟩ => ⟨(h hx).trans hz, hx⟩⟩
  rw [← he]
  apply Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr limitResidual_mem_orthogonal)

/-- Orthogonal decomposition of the Hilbert model of the middle cokernel. -/
theorem constantLine_sup_common :
    Submodule.span ℝ {hilbertOne} ⊔ commonMeanOrthogonal =
      (LinearMap.range centerLegal.toLinearMap)ᗮ := by
  have he : (Submodule.span ℝ {hilbertOne})ᗮ ⊓
      (LinearMap.range centerLegal.toLinearMap)ᗮ = commonMeanOrthogonal := by
    rw [← meanZero_eq_orthogonal, centerLegal_range, ← Submodule.inf_orthogonal,
      ← defectLine_orthogonal_inf]
    ac_rfl
  rw [← he]
  apply Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
  apply Submodule.span_le.mpr
  apply Set.singleton_subset_iff.mpr
  rintro x ⟨v, rfl⟩
  exact (real_inner_comm _ _).trans (center_mem v.val)

/-- The middle quotient arrow also has the topology induced by the Hilbert norms. -/
def toCenterCokernelContinuous : BoundaryTarget →L[ℝ] CenterCokernel where
  __ := toCenterCokernel
  cont := by
    apply mixedInMeanZero.isQuotientMap_mkQL.continuous_iff.mpr
    exact (LinearMap.range centerLegal.toLinearMap).mkQL.continuous.comp continuous_subtype_val

/-- On orthogonal representatives the middle quotient arrow drops the defect component. -/
theorem toCenterCokernel_defect_add (t : ℝ) (w : commonMeanOrthogonal) :
    toCenterCokernelContinuous (mixedInMeanZero.mkQ
      (t • defect + (⟨w.val, w.property.1⟩ : meanZero))) =
      (LinearMap.range centerLegal.toLinearMap).mkQ w.val := by
  have hd : (defect : ThresholdHilbert) ∈ LinearMap.range centerLegal.toLinearMap := by
    rw [centerLegal_range]
    exact Submodule.mem_sup.mpr ⟨0, mixedClosure.zero_mem, _,
      Submodule.subset_span (Set.mem_singleton _), zero_add _⟩
  change (LinearMap.range centerLegal.toLinearMap).mkQ
    (t • (defect : ThresholdHilbert) + w.val) = _
  have hq : (LinearMap.range centerLegal.toLinearMap).mkQ (defect : ThresholdHilbert) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hd
  rw [map_add, map_smul, hq, smul_zero, zero_add]

/-- On the common summand the ambient projection is the identity. On the defect it
acts by the negative residual of the constant. -/
theorem legalOrthogonalProjection_defect_add (t : ℝ) (w : commonMeanOrthogonal) :
    closedSpaceᗮ.starProjection (t • (defect : ThresholdHilbert) + w.val) =
      -(t • limitResidual) + w.val := by
  have hu : normalizedScreenedTwo ∈ closedSpace :=
    screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
  have hu' : closedSpaceᗮ.starProjection normalizedScreenedTwo = 0 := by
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr hu,
      sub_self]
  have hd : closedSpaceᗮ.starProjection (defect : ThresholdHilbert) = -limitResidual := by
    change closedSpaceᗮ.starProjection (normalizedScreenedTwo - hilbertOne) = -limitResidual
    rw [map_sub, hu', zero_sub, Submodule.starProjection_orthogonal_val]
    rfl
  rw [map_add, map_smul, hd, smul_neg, Submodule.starProjection_eq_self_iff.mpr w.property.2]

/-- The squared norm of the transported boundary at one equals the legal projection error. -/
theorem transported_boundary_one_norm_sq :
    ‖boundaryTargetContinuousEquivLegalQuotient (boundary 1)‖ ^ 2 = limitEnergy := by
  change ‖boundaryTargetEquivLegalQuotient (boundary 1)‖ ^ 2 = _
  rw [boundaryTargetEquivLegalQuotient_boundary, one_smul, norm_neg, energy_eq_dist_sq]
  exact congrArg (fun t : ℝ => t ^ 2)
    (QuotientAddGroup.norm_mk (S := closedSpace.toAddSubgroup) hilbertOne)

/-- Classification and norm of all real-linear bounded sections in the ambient row. -/
theorem ambientMeanSection_graph (s : ℝ →L[ℝ] ThresholdHilbert)
    (hs : hilbertMeanContinuous.comp s = ContinuousLinearMap.id ℝ ℝ) :
    ∃! z : meanZero, (∀ t, s t = t • (hilbertOne + (z : ThresholdHilbert))) ∧
      ‖s‖ ^ 2 = 1 + ‖z‖ ^ 2 := by
  have h1 : hilbertMeanContinuous (s 1) = 1 := DFunLike.congr_fun hs 1
  let z : meanZero := ⟨s 1 - hilbertOne, by
    change hilbertMeanContinuous (s 1 - hilbertOne) = 0
    rw [map_sub, h1]
    simp⟩
  have hz : hilbertOne + (z : ThresholdHilbert) = s 1 := by
    change hilbertOne + (s 1 - hilbertOne) = s 1
    abel
  have hsval (t : ℝ) : s t = t • s 1 := by
    simpa only [smul_eq_mul, mul_one] using (s.map_smul t (1 : ℝ))
  have hnorm : ‖s‖ = ‖s 1‖ := by
    have he : s = ContinuousLinearMap.toSpanSingleton ℝ (s 1) :=
      ContinuousLinearMap.ext (fun t => hsval t)
    exact (congrArg norm he).trans (ContinuousLinearMap.norm_toSpanSingleton _)
  refine ⟨z, ⟨fun t => (hsval t).trans (congrArg (t • ·) hz.symm), ?_⟩, ?_⟩
  · rw [hnorm, ← hz, norm_add_sq_real, hilbertOne_norm_sq,
      show inner ℝ hilbertOne z.val = 0 from z.property]
    change 1 + 2 * 0 + ‖z‖ ^ 2 = 1 + ‖z‖ ^ 2
    ring
  · intro w hw
    have hw1 : s 1 = hilbertOne + (w : ThresholdHilbert) := by simpa using hw.1 1
    exact Subtype.ext (add_left_cancel (hw1.symm.trans hz.symm))

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
