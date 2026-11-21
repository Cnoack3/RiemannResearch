import RiemannResearch.RH.MixedConductorSplitExact
import RiemannResearch.RH.MixedConductorMetricLifting
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.ThresholdContractiveRepair
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The snake boundary for the centered Pareto mean

Centering the inclusion of the legal space into the ambient Hilbert space gives
a map of the two mean sequences with zero right vertical map. Its snake boundary
takes a scalar to its multiple of the class of the screened unit minus the ambient
constant. All norms use the original Pareto inner product and its quotient norm.

Source: the centered comparison proposed in the research discussion. The diagram
chase uses mathlib's module snake lemma (Stacks Project, Tag 07JV,
https://stacks.math.columbia.edu/tag/07JV). The metric statements use the Pareto
rank-one and energy identities. Vanishing of the boundary remains open. For the
reverse link with RH, Báez-Duarte's Theorem 1.1 (https://arxiv.org/abs/math/0202141)
supplies the natural-approximation implication appearing as a parameter.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

open CoefficientStabilization

/-- The mean-zero subspace of the ambient Pareto Hilbert space. -/
abbrev meanZero : Submodule ℝ ThresholdHilbert := hilbertMeanContinuous.ker

theorem meanZero_eq_orthogonal :
    meanZero = (Submodule.span ℝ {hilbertOne})ᗮ := by
  ext x
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right
    (𝕜 := ℝ) (u := hilbertOne) (v := x)).symm

private theorem mean_legal (x : closedSpace) :
    hilbertMeanContinuous (x : ThresholdHilbert) = legalPacketMean x := by
  change inner ℝ hilbertOne (x : ThresholdHilbert) = inner ℝ (x : ThresholdHilbert) hilbertOne
  exact real_inner_comm _ _

private theorem mean_screened : hilbertMeanContinuous normalizedScreenedTwo = 1 :=
  (real_inner_comm _ _).trans normalizedScreenedTwo_mean

instance meanZero_complete : CompleteSpace meanZero :=
  hilbertMeanContinuous.isClosed_ker.completeSpace_coe

/-- Subtract the ambient constant with the same mean. -/
def center : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ContinuousLinearMap.id ℝ _ - hilbertMeanContinuous.smulRight hilbertOne

theorem center_apply (x : ThresholdHilbert) :
    center x = x - hilbertMeanContinuous x • hilbertOne := rfl

theorem center_mem (x : ThresholdHilbert) : center x ∈ meanZero := by
  change hilbertMeanContinuous (x - hilbertMeanContinuous x • hilbertOne) = 0
  simp

theorem center_eq_starProjection : center = meanZero.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (center_mem x)
  intro y hy
  change inner ℝ (x - (x - hilbertMeanContinuous x • hilbertOne)) y = 0
  rw [sub_sub_cancel, real_inner_smul_left, show inner ℝ hilbertOne y = 0 from hy, mul_zero]

private theorem center_fixes {x : ThresholdHilbert} (hx : x ∈ meanZero) : center x = x := by
  rw [center_apply, show hilbertMeanContinuous x = 0 from hx, zero_smul, sub_zero]

/-- The middle vertical map in the comparison of mean sequences. -/
def centerLegal : closedSpace →L[ℝ] ThresholdHilbert := center.comp closedSpace.subtypeL

/-- The left vertical map includes a mixed vector into the ambient mean kernel. -/
def mixedInclusion : mixedClosure →L[ℝ] meanZero :=
  mixedClosure.subtypeL.codRestrict meanZero fun m =>
    (real_inner_comm _ _).trans
      ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp m.property).2

/-- The denominator of the cokernel, viewed inside the mean-zero subspace. -/
def mixedInMeanZero : Submodule ℝ meanZero := mixedClosure.comap meanZero.subtype

instance mixedInMeanZero_closed : IsClosed (mixedInMeanZero : Set meanZero) :=
  (show IsClosed (mixedClosure : Set ThresholdHilbert) from isClosed_closure).preimage
    continuous_subtype_val

instance mixedInMeanZero_complete : CompleteSpace mixedInMeanZero :=
  mixedInMeanZero_closed.completeSpace_coe

abbrev BoundaryTarget := meanZero ⧸ mixedInMeanZero

theorem legal_row_exact :
    Function.Exact legalMixedInclusion.toLinearMap legalPacketMean.toLinearMap := by
  intro x
  change legalPacketMean x = 0 ↔ ∃ m : mixedClosure, legalMixedInclusion m = x
  constructor
  · intro hx
    exact ⟨⟨x.val, (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
      ⟨x.property, hx⟩⟩, rfl⟩
  · rintro ⟨m, rfl⟩
    exact legalPacketMean_legalMixedInclusion m

theorem ambient_row_exact : Function.Exact meanZero.subtype hilbertMeanContinuous.toLinearMap :=
  LinearMap.exact_subtype_ker_map _

theorem ambient_mean_surjective : Function.Surjective hilbertMeanContinuous := by
  intro a
  exact ⟨a • hilbertOne, by simp⟩

theorem left_square :
    meanZero.subtype.comp mixedInclusion.toLinearMap =
      centerLegal.toLinearMap.comp legalMixedInclusion.toLinearMap := by
  apply LinearMap.ext
  intro m
  exact (center_fixes (mixedInclusion m).property).symm

theorem right_square :
    hilbertMeanContinuous.toLinearMap.comp centerLegal.toLinearMap =
      (0 : ℝ →ₗ[ℝ] ℝ).comp legalPacketMean.toLinearMap := by
  apply LinearMap.ext
  intro v
  exact center_mem (v : ThresholdHilbert)

section Diagram

open CategoryTheory CategoryTheory.Limits

/-- The lower row as a short complex of real topological vector spaces. -/
def ambientMeanComplex : ShortComplex (TopModuleCat ℝ) :=
  ShortComplex.mk (TopModuleCat.ofHom meanZero.subtypeL) (TopModuleCat.ofHom hilbertMeanContinuous)
    (by
      apply ConcreteCategory.hom_ext
      intro x
      exact x.property)

/-- Centering retracts onto the kernel, and the constant line splits the ambient mean. -/
def ambientMeanSplitting : ambientMeanComplex.Splitting where
  r := TopModuleCat.ofHom (center.codRestrict meanZero center_mem)
  s := TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton ℝ hilbertOne)
  f_r := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact center_fixes x.property
  s_g := by
    apply ConcreteCategory.hom_ext
    intro a
    change ℝ at a
    change hilbertMeanContinuous (a • hilbertOne) = a
    simp
  id := by
    apply ConcreteCategory.hom_ext
    intro x
    change ThresholdHilbert at x
    change (x - hilbertMeanContinuous x • hilbertOne) + hilbertMeanContinuous x • hilbertOne = x
    exact sub_add_cancel _ _

local instance : HasZeroObject (TopModuleCat.{0} ℝ) :=
  ⟨⟨_, (terminalIsTerminal (C := TopModuleCat.{0} ℝ)).isZero⟩⟩

theorem ambientMean_shortExact : ambientMeanComplex.ShortExact := ambientMeanSplitting.shortExact

/-- The morphism of short exact rows with vertical components inclusion, centering, and zero. -/
def centeredDiagram : legalMeanComplex ⟶ ambientMeanComplex where
  τ₁ := TopModuleCat.ofHom mixedInclusion
  τ₂ := TopModuleCat.ofHom centerLegal
  τ₃ := 0
  comm₁₂ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun left_square x
  comm₂₃ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun right_square x

end Diagram

private theorem quotient_exact : Function.Exact mixedInclusion.toLinearMap mixedInMeanZero.mkQ := by
  intro x
  change (Submodule.Quotient.mk x : BoundaryTarget) = 0 ↔ ∃ m : mixedClosure, mixedInclusion m = x
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    exact ⟨⟨x.val, hx⟩, rfl⟩
  · rintro ⟨m, rfl⟩
    exact m.property

private theorem scalar_kernel_exact :
    Function.Exact (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (0 : ℝ →ₗ[ℝ] ℝ) :=
  (LinearMap.exact_zero_iff_surjective _ _).mpr Function.surjective_id

private def centerToKernel (x : ThresholdHilbert) : meanZero := ⟨center x, center_mem x⟩

/-- The actual mathlib snake connecting map of the two exact rows. -/
def snakeMap : ℝ →ₗ[ℝ] BoundaryTarget :=
  SnakeLemma.δ mixedInclusion.toLinearMap centerLegal.toLinearMap (0 : ℝ →ₗ[ℝ] ℝ)
    legalMixedInclusion.toLinearMap legalPacketMean.toLinearMap legal_row_exact
    meanZero.subtype hilbertMeanContinuous.toLinearMap ambient_row_exact left_square right_square
    screenedMeanSection (funext legalPacketMean_screenedMeanSection)
    centerToKernel (funext fun x => Subtype.ext (center_fixes x.property))
    LinearMap.id scalar_kernel_exact mixedInMeanZero.mkQ quotient_exact

/-- The orthogonal representative of the boundary at one, inside the mean kernel. -/
def defect : meanZero := ⟨normalizedScreenedTwo - hilbertOne, by
  change hilbertMeanContinuous (normalizedScreenedTwo - hilbertOne) = 0
  rw [map_sub, mean_screened, hilbertMeanContinuous_one, sub_self]⟩

theorem snakeMap_apply (a : ℝ) : snakeMap a = a • mixedInMeanZero.mkQ defect := by
  rw [← map_smul]
  change mixedInMeanZero.mkQ (centerToKernel (center (a • normalizedScreenedTwo))) = _
  apply congrArg mixedInMeanZero.mkQ
  apply Subtype.ext
  change center (center (a • normalizedScreenedTwo)) = a • (normalizedScreenedTwo - hilbertOne)
  rw [center_fixes (center_mem _), map_smul, center_apply, mean_screened, one_smul]

/-- The domain of the initial arrow is the legal part of the constant line. -/
abbrev legalConstants : Submodule ℝ closedSpace :=
  (Submodule.span ℝ {hilbertOne}).comap closedSpace.subtype

private theorem center_eq_zero_iff (x : ThresholdHilbert) :
    center x = 0 ↔ x ∈ Submodule.span ℝ {hilbertOne} := by
  rw [center_apply, sub_eq_zero, Submodule.mem_span_singleton]
  constructor
  · intro h
    exact ⟨hilbertMeanContinuous x, h.symm⟩
  · rintro ⟨a, rfl⟩
    simp

private theorem legalConstants_exact :
    Function.Exact legalConstants.subtype centerLegal.toLinearMap := by
  intro x
  change center (x : ThresholdHilbert) = 0 ↔ ∃ y : legalConstants, (y : closedSpace) = x
  rw [center_eq_zero_iff]
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩

/-- The mean on the legal part of the constant line. -/
def constantMean : legalConstants →ₗ[ℝ] ℝ := legalPacketMean.toLinearMap.comp legalConstants.subtype

theorem constantMean_injective : Function.Injective constantMean := by
  have hval (x : legalConstants) :
      ((x : closedSpace) : ThresholdHilbert) = constantMean x • hilbertOne := by
    have hx : center ((x : closedSpace) : ThresholdHilbert) = 0 :=
      (center_eq_zero_iff _).mpr x.property
    rw [center_apply, sub_eq_zero, mean_legal] at hx
    exact hx
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact (hval x).trans ((congrArg (fun a : ℝ => a • hilbertOne) h).trans (hval y).symm)

theorem exact_constantMean_snakeMap : Function.Exact constantMean snakeMap := by
  unfold snakeMap
  apply SnakeLemma.exact_δ_right (ι₂ := legalConstants.subtype) (hι₂ := legalConstants_exact)
  · rfl
  · exact Function.injective_id

/-- The continuous realization of the algebraic snake map with the quotient norm. -/
def boundary : ℝ →L[ℝ] BoundaryTarget :=
  ContinuousLinearMap.toSpanSingleton ℝ (mixedInMeanZero.mkQ defect)

theorem boundary_apply (a : ℝ) : boundary a = a • mixedInMeanZero.mkQ defect := rfl

theorem boundary_toLinearMap : boundary.toLinearMap = snakeMap := by
  apply LinearMap.ext
  intro a
  exact (snakeMap_apply a).symm

/-- Any legal lift gives the same cokernel class after centering. -/
theorem boundary_of_lift (v : closedSpace) :
    boundary (legalPacketMean v) = mixedInMeanZero.mkQ ⟨center v.val, center_mem v.val⟩ := by
  change boundary.toLinearMap (legalPacketMean v) = _
  rw [boundary_toLinearMap]
  unfold snakeMap
  apply SnakeLemma.δ_eq (y := v)
  · rfl
  · rfl

/-- Exactness at the scalar line in the continuous realization. -/
theorem exact_constantMean_boundary : Function.Exact constantMean boundary := by
  change Function.Exact constantMean boundary.toLinearMap
  rw [boundary_toLinearMap]
  exact exact_constantMean_snakeMap

theorem defect_orthogonal : defect ∈ mixedInMeanZeroᗮ := by
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  have hd := mixedClosure.orthogonal.sub_mem hu.2 one_mem_mixedClosure_orthogonal
  intro m hm
  exact hd (m : ThresholdHilbert) hm

/-- The excess squared norm of any other representative is its squared distance from the defect. -/
theorem norm_sq_of_same_class (z : meanZero)
    (hz : mixedInMeanZero.mkQ z = mixedInMeanZero.mkQ defect) :
    ‖z‖ ^ 2 = ‖defect‖ ^ 2 + ‖z - defect‖ ^ 2 := by
  have hm : z - defect ∈ mixedInMeanZero := by
    apply (Submodule.Quotient.mk_eq_zero mixedInMeanZero).mp
    change mixedInMeanZero.mkQ (z - defect) = 0
    rw [map_sub, hz, sub_self]
  have ho := defect_orthogonal (z - defect) hm
  calc
    ‖z‖ ^ 2 = ‖(z - defect) + defect‖ ^ 2 := by rw [sub_add_cancel]
    _ = _ := by rw [norm_add_sq_real, ho]; ring

theorem norm_defect_class :
    ‖mixedInMeanZero.mkQ defect‖ = ‖normalizedScreenedTwo - hilbertOne‖ := by
  calc
    _ = Metric.infDist defect (mixedInMeanZero : Set meanZero) :=
      QuotientAddGroup.norm_mk (S := mixedInMeanZero.toAddSubgroup) defect
    _ = ‖defect - mixedInMeanZero.starProjection defect‖ :=
      mixedInMeanZero.infDist_eq_norm_sub_starProjection defect
    _ = _ := by
      rw [(mixedInMeanZero.starProjection_apply_eq_zero_iff).mpr defect_orthogonal, sub_zero]
      rfl

theorem boundary_norm : ‖boundary‖ = ‖normalizedScreenedTwo - hilbertOne‖ :=
  (ContinuousLinearMap.norm_toSpanSingleton _).trans norm_defect_class

theorem boundary_norm_sq : ‖boundary‖ ^ 2 = ‖normalizedScreenedTwo‖ ^ 2 - 1 := by
  rw [boundary_norm, norm_sub_sq_real, normalizedScreenedTwo_mean, hilbertOne_norm_sq]
  ring

/-- Exact conversion between the norm of the snake boundary and the legal projection error. -/
theorem boundary_norm_sq_eq_energy : ‖boundary‖ ^ 2 = limitEnergy / (1 - limitEnergy) := by
  rw [boundary_norm_sq, normalizedScreenedTwo_norm_sq]
  field_simp [one_sub_limitEnergy_pos.ne']
  ring

theorem boundary_eq_zero_iff_screened : boundary = 0 ↔ normalizedScreenedTwo = hilbertOne := by
  calc
    _ ↔ ‖boundary‖ = 0 := norm_eq_zero.symm
    _ ↔ _ := by rw [boundary_norm, norm_eq_zero, sub_eq_zero]

theorem boundary_eq_zero_iff_one_mem : boundary = 0 ↔ hilbertOne ∈ closedSpace :=
  boundary_eq_zero_iff_screened.trans one_mem_closedSpace_iff_normalizedScreenedTwo.symm

theorem boundary_range :
    LinearMap.range boundary.toLinearMap = Submodule.span ℝ {mixedInMeanZero.mkQ defect} := by
  ext x
  change (∃ a : ℝ, boundary a = x) ↔ _
  rw [Submodule.mem_span_singleton]
  simp only [boundary_apply]

theorem boundary_injective_iff : Function.Injective boundary ↔ hilbertOne ∉ closedSpace := by
  constructor
  · intro hi h
    have he : boundary 0 = boundary 1 := by rw [boundary_eq_zero_iff_one_mem.mpr h]; rfl
    exact zero_ne_one (hi he)
  · intro h
    have hd : mixedInMeanZero.mkQ defect ≠ 0 := by
      intro he
      apply h
      apply boundary_eq_zero_iff_one_mem.mp
      apply ContinuousLinearMap.ext
      intro a
      simp [boundary_apply, he]
    intro a b hab
    have he : (a - b) • mixedInMeanZero.mkQ defect = 0 := by
      rw [← boundary_apply, map_sub, hab, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hd)

theorem legalConstants_eq_bot_of_nonmember (h : hilbertOne ∉ closedSpace) : legalConstants = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  let z : legalConstants := ⟨v, hv⟩
  have hz := exact_constantMean_boundary.apply_apply_eq_zero z
  have hmean : constantMean z = 0 := boundary_injective_iff.mpr h (hz.trans boundary.map_zero.symm)
  have hzero : z = 0 := constantMean_injective (hmean.trans constantMean.map_zero.symm)
  exact (Submodule.mem_bot ℝ).mpr (congrArg (fun x : legalConstants => (x : closedSpace)) hzero)

theorem boundary_rank_one_of_nonmember (h : hilbertOne ∉ closedSpace) :
    Module.finrank ℝ (LinearMap.range boundary.toLinearMap) = 1 := by
  let e := LinearEquiv.ofInjective boundary.toLinearMap (boundary_injective_iff.mpr h)
  simpa using e.symm.finrank_eq

theorem energy_eq_dist_sq :
    limitEnergy = Metric.infDist hilbertOne (closedSpace : Set ThresholdHilbert) ^ 2 := by
  rw [closedSpace.infDist_eq_norm_sub_starProjection]
  rfl

theorem energy_le_legal_error (v : closedSpace) :
    limitEnergy ≤ ‖hilbertOne - (v : ThresholdHilbert)‖ ^ 2 := by
  rw [energy_eq_dist_sq]
  have h := Metric.infDist_le_dist_of_mem (x := hilbertOne) v.property
  rw [dist_eq_norm] at h
  exact pow_le_pow_left₀ Metric.infDist_nonneg h 2

/-- The minimum over the legal mean-one fiber is attained by the screened section at one. -/
theorem meanOne_norm_minimum :
    IsLeast {r : ℝ | ∃ v : closedSpace, legalPacketMean v = 1 ∧ ‖v‖ = r}
      ‖normalizedScreenedTwo‖ := by
  constructor
  · refine ⟨screenedMeanSection 1, legalPacketMean_screenedMeanSection _, ?_⟩
    change ‖(1 : ℝ) • normalizedScreenedTwo‖ = _
    rw [one_smul]
  · rintro _ ⟨v, hv, rfl⟩
    simpa [hv] using legalPacketMean_fiber_bound v

/-- In the nonmembership branch the boundary is an injection onto a line, with a positive
uniform legal error and a strictly superunit least norm on the mean-one fiber. -/
theorem nonzero_branch (h : hilbertOne ∉ closedSpace) :
    boundary.ker = ⊥ ∧ Module.finrank ℝ (LinearMap.range boundary.toLinearMap) = 1 ∧
      0 < limitEnergy ∧ 0 < ‖boundary‖ ^ 2 ∧ 1 < ‖normalizedScreenedTwo‖ := by
  have hE : 0 < limitEnergy := lt_of_le_of_ne (sq_nonneg ‖limitResidual‖)
    (fun he => h (limitEnergy_zero_iff_mem.mp he.symm))
  have hz : boundary ≠ 0 := fun he => h (boundary_eq_zero_iff_one_mem.mp he)
  exact ⟨LinearMap.ker_eq_bot.mpr (boundary_injective_iff.mpr h),
    boundary_rank_one_of_nonmember h, hE, sq_pos_of_pos (norm_pos_iff.mpr hz),
    one_lt_norm_normalizedScreenedTwo_iff.mpr hE⟩

theorem boundary_eq_zero_iff_naturalApproximation :
    boundary = 0 ↔ BaezDuarte.NaturalApproximation :=
  boundary_eq_zero_iff_one_mem.trans BaezDuarte.naturalApproximation_iff_one_mem.symm

theorem riemannHypothesis_of_boundary_eq_zero (h : boundary = 0) : RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo (boundary_eq_zero_iff_screened.mp h)

/-- The converse uses the published RH-to-natural-approximation implication as a parameter. -/
theorem boundary_injective_iff_not_riemannHypothesis
    (hBD : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    Function.Injective boundary ↔ ¬ RiemannHypothesis := by
  have hm : hilbertOne ∈ closedSpace ↔ RiemannHypothesis :=
    ⟨fun h => riemannHypothesis_of_boundary_eq_zero (boundary_eq_zero_iff_one_mem.mpr h),
      fun h => BaezDuarte.naturalApproximation_iff_one_mem.mp (hBD h)⟩
  exact boundary_injective_iff.trans hm.not

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
