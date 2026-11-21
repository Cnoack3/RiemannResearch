import RiemannResearch.RH.CenteredMeanSnake
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MixedConductorSplitExact
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.PrimePowerRamanujanClosure
import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.RH.ThresholdContractiveRepair
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-!
# The internal and ambient quotients for the Pareto mean

The projected constant represents the legal mean on the closed space `V`.
The quotient of its orthogonal complement inside `V` by the mixed subspace is
zero. In the ambient space, inclusion identifies the target of the centered
snake boundary with `H ⧸ V`. Under this identification the boundary at one is
the negative of the class of the constant. The boundary vanishes exactly when the
mixed space is the full ambient orthogonal complement of the constant. Inside
`V`, the projected constant and the screened unit have the same orthogonal complement.

Source: the user's comparison of the two mean quotients and the rank-one formula.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

open CoefficientStabilization

/-- The ambient constant projected orthogonally into the legal space. -/
def projectedOne : closedSpace := ⟨limitProjection, closedSpace.starProjection_apply_mem _⟩

theorem inner_projectedOne (v : closedSpace) :
    inner ℝ v projectedOne = legalPacketMean v := by
  have h := limitResidual_mem_orthogonal (v : ThresholdHilbert) v.property
  change inner ℝ (v : ThresholdHilbert) (hilbertOne - limitProjection) = 0 at h
  rw [inner_sub_right, sub_eq_zero] at h
  exact h.symm

/-- The orthogonal complement here is formed in the legal Hilbert space. -/
theorem projectedOne_orthogonal_eq_mixed :
    (Submodule.span ℝ {projectedOne})ᗮ = mixedClosure.comap closedSpace.subtype := by
  rw [← legalPacketMean_ker]
  ext v
  change v ∈ (Submodule.span ℝ {projectedOne})ᗮ ↔ legalPacketMean v = 0
  simp only [Submodule.mem_orthogonal_singleton_iff_inner_right, ← inner_projectedOne,
    real_inner_comm]

/-- Inside the legal space the projected constant is the screened section at one
scaled by the reciprocal squared norm of its ambient value. -/
theorem projectedOne_eq_scaled_section_one :
    projectedOne = (‖normalizedScreenedTwo‖ ^ 2)⁻¹ • screenedMeanSection 1 := by
  apply Subtype.ext
  change limitProjection = (‖normalizedScreenedTwo‖ ^ 2)⁻¹ • ((1 : ℝ) • normalizedScreenedTwo)
  simpa only [one_smul] using limitProjection_eq_inv_norm_sq_smul_screenedTwo

/-- The orthogonal complement of the screened unit inside the legal space is the mixed space. -/
theorem screenedMeanSection_one_orthogonal_eq_mixed :
    (Submodule.span ℝ {screenedMeanSection 1})ᗮ = mixedClosure.comap closedSpace.subtype := by
  have hpos : 0 < ‖normalizedScreenedTwo‖ :=
    zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo
  have hunit : IsUnit ((‖normalizedScreenedTwo‖ ^ 2)⁻¹) :=
    isUnit_iff_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hpos.ne'))
  rw [← projectedOne_orthogonal_eq_mixed, projectedOne_eq_scaled_section_one,
    Submodule.span_singleton_smul_eq hunit]

/-- The quotient of the legal orthogonal complement of the projected constant by the mixed space. -/
abbrev InternalMeanQuotient :=
  (Submodule.span ℝ {projectedOne})ᗮ ⧸
    (mixedClosure.comap closedSpace.subtype).comap (Submodule.span ℝ {projectedOne})ᗮ.subtype

theorem internalMeanQuotient_subsingleton : Subsingleton InternalMeanQuotient := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro v _
  change (v : closedSpace) ∈ mixedClosure.comap closedSpace.subtype
  rw [← projectedOne_orthogonal_eq_mixed]
  exact v.property

/-- The screened unit is the normalized projection of the conductor-two packet. -/
theorem normalizedScreenedTwo_eq_projected_packet :
    normalizedScreenedTwo =
      (Real.log 2)⁻¹ • mixedClosureᗮ.starProjection (ramanujanPacketHilbert 2) := by
  change (Real.log 2)⁻¹ • (ramanujanPacketHilbert 2 -
    mixedClosure.starProjection (ramanujanPacketHilbert 2)) = _
  rw [Submodule.starProjection_orthogonal_val]

/-- On a legal vector the projection onto the ambient mixed orthogonal complement has rank one. -/
theorem mixedOrthogonal_starProjection_legal (v : closedSpace) :
    mixedClosureᗮ.starProjection (v : ThresholdHilbert) =
      inner ℝ v projectedOne • normalizedScreenedTwo := by
  rw [inner_projectedOne, Submodule.starProjection_orthogonal_val]
  exact fullScreening_eq_mean_smul v.property

/-- Kernel and range of the orthogonal projection onto the mixed complement restricted to `V`. -/
theorem legalScreening_ker_range :
    (mixedClosureᗮ.starProjection.comp closedSpace.subtypeL).ker =
        mixedClosure.comap closedSpace.subtype ∧
      LinearMap.range (mixedClosureᗮ.starProjection.comp closedSpace.subtypeL).toLinearMap =
        Submodule.span ℝ {normalizedScreenedTwo} := by
  constructor
  · rw [← legalPacketMean_ker]
    ext v
    change mixedClosureᗮ.starProjection (v : ThresholdHilbert) = 0 ↔ legalPacketMean v = 0
    rw [mixedOrthogonal_starProjection_legal, inner_projectedOne]
    have hu : normalizedScreenedTwo ≠ 0 :=
      norm_pos_iff.mp (zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo)
    simp [hu]
  · ext x
    change (∃ v : closedSpace, mixedClosureᗮ.starProjection (v : ThresholdHilbert) = x) ↔ _
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨inner ℝ v projectedOne, (mixedOrthogonal_starProjection_legal v).symm⟩
    · rintro ⟨a, rfl⟩
      refine ⟨screenedMeanSection a, ?_⟩
      rw [mixedOrthogonal_starProjection_legal, inner_projectedOne,
        legalPacketMean_screenedMeanSection]

/-- The mixed space and the screened line sum to the legal space and are orthogonal. -/
theorem legal_mixed_screened_orthogonal_sum :
    mixedClosure ⊔ Submodule.span ℝ {normalizedScreenedTwo} = closedSpace ∧
      Submodule.span ℝ {normalizedScreenedTwo} ≤ mixedClosureᗮ := by
  rw [← screenedPrimeClosure_eq_span_two]
  refine ⟨mixed_sup_screenedPrimeClosure, ?_⟩
  rw [screenedPrimeClosure_eq_inf_orthogonal]
  exact inf_le_right

/-- The two orthogonal components of the ambient constant, with its legal component evaluated. -/
theorem one_eq_screened_add_orthogonal :
    hilbertOne = (‖normalizedScreenedTwo‖ ^ 2)⁻¹ • normalizedScreenedTwo +
      closedSpaceᗮ.starProjection hilbertOne := by
  rw [← limitProjection_eq_inv_norm_sq_smul_screenedTwo, Submodule.starProjection_orthogonal_val]
  change hilbertOne = limitProjection + (hilbertOne - limitProjection)
  exact (add_sub_cancel _ _).symm

/-- Inclusion of the ambient mean-zero hyperplane followed by the quotient by the legal space. -/
def meanZeroToLegalQuotient : meanZero →ₗ[ℝ] ThresholdHilbert ⧸ closedSpace :=
  closedSpace.mkQ.comp meanZero.subtype

theorem meanZeroToLegalQuotient_ker : meanZeroToLegalQuotient.ker = mixedInMeanZero := by
  ext x
  change (Submodule.Quotient.mk (x : ThresholdHilbert) : ThresholdHilbert ⧸ closedSpace) = 0 ↔
    (x : ThresholdHilbert) ∈ mixedClosure
  rw [Submodule.Quotient.mk_eq_zero, mem_mixedClosure_iff_mem_closedSpace_and_mean_zero]
  have hx : inner ℝ (x : ThresholdHilbert) hilbertOne = 0 :=
    (real_inner_comm _ _).trans x.property
  exact ⟨fun hv => ⟨hv, hx⟩, And.left⟩

/-- Subtract the legal vector with the prescribed mean in the screened line. -/
def meanZeroRepresentative (x : ThresholdHilbert) : meanZero :=
  ⟨x - hilbertMeanContinuous x • normalizedScreenedTwo, by
    have hu : hilbertMeanContinuous normalizedScreenedTwo = 1 :=
      (real_inner_comm _ _).trans normalizedScreenedTwo_mean
    change hilbertMeanContinuous (x - hilbertMeanContinuous x • normalizedScreenedTwo) = 0
    simp [hu]⟩

private theorem mkQ_screenedTwo : closedSpace.mkQ normalizedScreenedTwo = 0 :=
  (Submodule.Quotient.mk_eq_zero closedSpace).mpr
    (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure)

@[simp] theorem meanZeroToLegalQuotient_representative (x : ThresholdHilbert) :
    meanZeroToLegalQuotient (meanZeroRepresentative x) = closedSpace.mkQ x := by
  change closedSpace.mkQ (x - hilbertMeanContinuous x • normalizedScreenedTwo) = _
  rw [map_sub, map_smul, mkQ_screenedTwo, smul_zero, sub_zero]

theorem meanZeroToLegalQuotient_surjective : Function.Surjective meanZeroToLegalQuotient := by
  intro q
  obtain ⟨x, rfl⟩ := closedSpace.mkQ_surjective q
  exact ⟨meanZeroRepresentative x, meanZeroToLegalQuotient_representative x⟩

/-- Inclusion induces the linear equivalence from the snake target to the legal quotient. -/
def boundaryTargetEquivLegalQuotient : BoundaryTarget ≃ₗ[ℝ] ThresholdHilbert ⧸ closedSpace :=
  (Submodule.quotEquivOfEq _ _ meanZeroToLegalQuotient_ker.symm).trans
    (meanZeroToLegalQuotient.quotKerEquivOfSurjective meanZeroToLegalQuotient_surjective)

@[simp] theorem boundaryTargetEquivLegalQuotient_mk (x : meanZero) :
    boundaryTargetEquivLegalQuotient (mixedInMeanZero.mkQ x) =
      closedSpace.mkQ (x : ThresholdHilbert) := rfl

theorem boundaryTargetEquivLegalQuotient_symm_mk (x : ThresholdHilbert) :
    boundaryTargetEquivLegalQuotient.symm (closedSpace.mkQ x) =
      mixedInMeanZero.mkQ (meanZeroRepresentative x) := by
  apply boundaryTargetEquivLegalQuotient.injective
  rw [LinearEquiv.apply_symm_apply, boundaryTargetEquivLegalQuotient_mk]
  exact (meanZeroToLegalQuotient_representative x).symm

/-- The boundary of a scalar becomes the negative of the corresponding constant class. -/
@[simp] theorem boundaryTargetEquivLegalQuotient_boundary (a : ℝ) :
    boundaryTargetEquivLegalQuotient (boundary a) = -(a • closedSpace.mkQ hilbertOne) := by
  rw [boundary_apply, map_smul, boundaryTargetEquivLegalQuotient_mk]
  change a • closedSpace.mkQ (normalizedScreenedTwo - hilbertOne) = _
  rw [map_sub, mkQ_screenedTwo, zero_sub, smul_neg]

/-- The single boundary value at one detects membership of the ambient constant. -/
theorem boundary_one_eq_zero_iff_one_mem :
    boundary 1 = 0 ↔ hilbertOne ∈ closedSpace := by
  calc
    boundary 1 = 0 ↔ boundaryTargetEquivLegalQuotient (boundary 1) =
        boundaryTargetEquivLegalQuotient 0 := boundaryTargetEquivLegalQuotient.injective.eq_iff.symm
    _ ↔ hilbertOne ∈ closedSpace := by
      rw [map_zero, boundaryTargetEquivLegalQuotient_boundary, one_smul, neg_eq_zero]
      exact Submodule.Quotient.mk_eq_zero closedSpace

theorem boundaryTarget_subsingleton_iff_closedSpace_eq_top :
    Subsingleton BoundaryTarget ↔ closedSpace = ⊤ := by
  rw [← Submodule.Quotient.subsingleton_iff (p := closedSpace)]
  let e := boundaryTargetEquivLegalQuotient
  exact ⟨fun h => ⟨fun _ _ => e.symm.injective (h.elim _ _)⟩,
    fun h => ⟨fun _ _ => e.injective (h.elim _ _)⟩⟩

/-- The ambient quotient vanishes exactly when the constant belongs to the legal space. -/
theorem boundaryTarget_subsingleton_iff_one_mem :
    Subsingleton BoundaryTarget ↔ hilbertOne ∈ closedSpace :=
  boundaryTarget_subsingleton_iff_closedSpace_eq_top.trans closedSpace_eq_top_iff_one_mem

/-- As an ambient subspace, the mixed closure is the legal part of the constant's orthogonal
complement. -/
theorem mixedClosure_eq_closedSpace_inf_one_orthogonal :
    mixedClosure = closedSpace ⊓ (Submodule.span ℝ {hilbertOne})ᗮ := by
  ext x
  simp only [mem_mixedClosure_iff_mem_closedSpace_and_mean_zero, Submodule.mem_inf,
    Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]

/-- The screened unit minus the ambient constant has mean zero and is orthogonal to every
mixed vector. Both complements in this statement are formed in the ambient space. -/
theorem screenedTwo_sub_one_mem_orthogonals :
    normalizedScreenedTwo - hilbertOne ∈
      (Submodule.span ℝ {hilbertOne})ᗮ ⊓ mixedClosureᗮ := by
  constructor
  · rw [← meanZero_eq_orthogonal]
    exact defect.property
  · intro m hm
    exact defect_orthogonal (mixedInclusion ⟨m, hm⟩) hm

/-- The missing inclusion puts the defect in the mixed space as well as its orthogonal
complement, so the screened unit equals the constant. -/
theorem screenedTwo_eq_one_of_one_orthogonal_le_mixed
    (h : (Submodule.span ℝ {hilbertOne})ᗮ ≤ mixedClosure) :
    normalizedScreenedTwo = hilbertOne := by
  have hd := screenedTwo_sub_one_mem_orthogonals
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hd.2 _ (h hd.1)))

/-- In the converse direction, legality of the constant gives density via the scaled
dilation differences for the coordinate point masses. -/
theorem one_orthogonal_le_mixedClosure_iff_one_mem :
    (Submodule.span ℝ {hilbertOne})ᗮ ≤ mixedClosure ↔ hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    exact one_mem_closedSpace_iff_normalizedScreenedTwo.mpr
      (screenedTwo_eq_one_of_one_orthogonal_le_mixed h)
  · intro hOne
    simp only [mixedClosure_eq_closedSpace_inf_one_orthogonal,
      closedSpace_eq_top_iff_one_mem.mpr hOne, top_inf_eq, le_refl]

theorem closedSpace_eq_top_iff_mixedClosure_eq_one_orthogonal :
    closedSpace = ⊤ ↔ mixedClosure = (Submodule.span ℝ {hilbertOne})ᗮ := by
  constructor
  · intro h
    rw [mixedClosure_eq_closedSpace_inf_one_orthogonal, h, top_inf_eq]
  · intro h
    exact closedSpace_eq_top_iff_one_mem.mpr (one_orthogonal_le_mixedClosure_iff_one_mem.mp h.ge)

/-- Vanishing of the centered snake boundary is equivalent to equality of the two ambient
subspaces. -/
theorem boundary_eq_zero_iff_mixedClosure_eq_one_orthogonal :
    boundary = 0 ↔ mixedClosure = (Submodule.span ℝ {hilbertOne})ᗮ :=
  boundary_eq_zero_iff_one_mem.trans
    (closedSpace_eq_top_iff_one_mem.symm.trans closedSpace_eq_top_iff_mixedClosure_eq_one_orthogonal)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
