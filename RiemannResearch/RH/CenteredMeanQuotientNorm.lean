import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import RiemannResearch.RH.CenteredMeanAmbientGeometry
import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.CenteredMeanSnake
import RiemannResearch.RH.CenteredMeanStageSnake
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.MixedConductorRankOne
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Norm distortion of the inclusion of the mean-zero quotient

The ordinary inclusion of the two mean sequences induces the map from `Z/M` to
`H/V` studied here. The centered boundary at one supplies its extremal vector.
The real Hilbert norms are the quotient norms on these two spaces.

The rank-one loss formula was proposed by Christian Noack. The proof uses the
orthogonal models in `CenteredMeanAmbientGeometry` and the rank-one projection
onto the screened line. At a support stage the third isomorphism identifies the
stage target isometrically with `Z/M`.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

open CoefficientStabilization

local notation "Φ" => boundaryTargetContinuousEquivLegalQuotient

local instance : (closedSpace ⊓ mixedClosureᗮ).HasOrthogonalProjection := by
  rw [← screenedPrimeClosure_eq_inf_orthogonal]
  infer_instance

/-- The mixed, screened and legal projections of the constant, and its ambient residual. -/
theorem one_projection_geometry :
    mixedClosure.starProjection hilbertOne = 0 ∧
    (closedSpace ⊓ mixedClosureᗮ).starProjection hilbertOne =
      (1 - limitEnergy) • normalizedScreenedTwo ∧
    closedSpace.starProjection hilbertOne - mixedClosure.starProjection hilbertOne =
      (1 - limitEnergy) • normalizedScreenedTwo ∧
    hilbertOne - closedSpace.starProjection hilbertOne =
      hilbertOne - (‖normalizedScreenedTwo‖ ^ 2)⁻¹ • normalizedScreenedTwo := by
  have hm := (mixedClosure.starProjection_apply_eq_zero_iff).mpr one_mem_mixedClosure_orthogonal
  have hv : closedSpace.starProjection hilbertOne = (1 - limitEnergy) • normalizedScreenedTwo :=
    limitProjection_eq_scaled_screenedTwo
  refine ⟨hm, ?_, by rw [hm, sub_zero, hv],
    congrArg (hilbertOne - ·) limitProjection_eq_inv_norm_sq_smul_screenedTwo⟩
  simpa only [← screenedPrimeClosure_eq_inf_orthogonal] using
    screenedPrimeClosure_starProjection_one.trans limitProjection_eq_scaled_screenedTwo

private theorem energy_mul_one_add_defect :
    limitEnergy * (1 + ‖defect‖ ^ 2) = ‖defect‖ ^ 2 := by
  have hd : ‖defect‖ ^ 2 = limitEnergy / (1 - limitEnergy) := by
    rw [show ‖defect‖ = ‖normalizedScreenedTwo - hilbertOne‖ from rfl, ← boundary_norm]
    exact boundary_norm_sq_eq_energy
  have h := (eq_div_iff one_sub_limitEnergy_pos.ne').mp hd
  nlinarith only [h]

open RiemannResearch.Analysis.NestedOrthogonalDecomposition in
/-- The difference of the legal and mixed projections is a rank-one operator on the mean-zero
hyperplane. This vector identity holds for every representative. -/
theorem legalProjection_sub_mixedProjection (z : meanZero) :
    closedSpace.starProjection z.val - mixedClosure.starProjection z.val =
      (inner ℝ z defect / (1 + ‖defect‖ ^ 2)) • normalizedScreenedTwo := by
  have h := fullScreening_eq_mean_smul (closedSpace.starProjection_apply_mem z.val)
  change closedSpace.starProjection z.val - mixedClosure.starProjection
    (closedSpace.starProjection z.val) =
      inner ℝ (closedSpace.starProjection z.val) hilbertOne • normalizedScreenedTwo at h
  have hi : inner ℝ z defect = inner ℝ z.val normalizedScreenedTwo := by
    change inner ℝ z.val (normalizedScreenedTwo - hilbertOne) = _
    rw [inner_sub_right, show inner ℝ z.val hilbertOne = 0 from
      (real_inner_comm _ _).trans z.property, sub_zero]
  have hc : (1 - limitEnergy) * (1 + ‖defect‖ ^ 2) = 1 := by
    nlinarith only [energy_mul_one_add_defect]
  rw [nested_projection_apply mixedClosure_le_closedSpace,
    closedSpace.inner_starProjection_left_eq_right, show closedSpace.starProjection hilbertOne =
      (1 - limitEnergy) • normalizedScreenedTwo from limitProjection_eq_scaled_screenedTwo,
    real_inner_smul_right] at h
  rw [h, hi]
  congr 1
  apply (eq_div_iff (by positivity)).mpr
  calc
    _ = ((1 - limitEnergy) * (1 + ‖defect‖ ^ 2)) * inner ℝ z.val normalizedScreenedTwo := by ring
    _ = _ := by rw [hc, one_mul]

private theorem norm_mk_orthogonalProjection {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : Submodule ℝ H) [K.HasOrthogonalProjection] (x : H) :
    ‖K.mkQ x‖ = ‖Kᗮ.starProjection x‖ := by
  rw [Submodule.starProjection_orthogonal_val]
  exact (QuotientAddGroup.norm_mk (S := K.toAddSubgroup) x).trans
    (K.infDist_eq_norm_sub_starProjection x)

private theorem defect_inner_common (w : commonMeanOrthogonal) :
    inner ℝ defect (⟨w.val, w.property.1⟩ : meanZero) = 0 := by
  change inner ℝ (normalizedScreenedTwo - hilbertOne) w.val = 0
  rw [inner_sub_left, w.property.2 _ (screenedPrimeClosure_le_closedSpace
    normalizedScreenedTwo_mem_screenedPrimeClosure),
    show inner ℝ hilbertOne w.val = 0 from w.property.1, sub_zero]

/-- Pythagoras in the domain and range. The two coordinates use the same common vector. -/
theorem quotient_norms_defect_add (t : ℝ) (w : commonMeanOrthogonal) :
    let q := mixedInMeanZero.mkQ (t • defect + (⟨w.val, w.property.1⟩ : meanZero))
    ‖q‖ ^ 2 = t ^ 2 * ‖defect‖ ^ 2 + ‖w‖ ^ 2 ∧
      ‖Φ q‖ ^ 2 = t ^ 2 * limitEnergy + ‖w‖ ^ 2 := by
  let wZ : meanZero := ⟨w.val, w.property.1⟩
  have hw : wZ ∈ mixedInMeanZeroᗮ :=
    fun m hm => w.property.2 m.val (mixedClosure_le_closedSpace hm)
  have hdw : inner ℝ defect wZ = 0 := defect_inner_common w
  have hrw : inner ℝ limitResidual w.val = 0 := by
    change inner ℝ (hilbertOne - limitProjection) w.val = 0
    rw [inner_sub_left, show inner ℝ hilbertOne w.val = 0 from w.property.1,
      show inner ℝ limitProjection w.val = 0 from
        w.property.2 limitProjection (closedSpace.starProjection_apply_mem _), sub_zero]
  constructor
  · change ‖mixedInMeanZero.mkQ (t • defect + wZ)‖ ^ 2 = _
    rw [norm_mk_orthogonalProjection,
      Submodule.starProjection_eq_self_iff.mpr
        (mixedInMeanZeroᗮ.add_mem (mixedInMeanZeroᗮ.smul_mem t defect_orthogonal) hw),
      norm_add_sq_real, real_inner_smul_left, hdw, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    change _ = t ^ 2 * ‖defect‖ ^ 2 + ‖wZ‖ ^ 2
    ring
  · change ‖closedSpace.mkQ (t • (defect : ThresholdHilbert) + w.val)‖ ^ 2 = _
    rw [norm_mk_orthogonalProjection, legalOrthogonalProjection_defect_add,
      norm_add_sq_real, inner_neg_left, real_inner_smul_left, hrw, norm_neg, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    change _ = t ^ 2 * ‖limitResidual‖ ^ 2 + ‖w.val‖ ^ 2
    ring

private theorem exists_mixed_defect_common (z : meanZero) :
    ∃ m ∈ mixedInMeanZero, ∃ (t : ℝ) (w : commonMeanOrthogonal),
      z = m + (t • defect + (⟨w.val, w.property.1⟩ : meanZero)) := by
  obtain ⟨m, hm, y, hy, rfl⟩ := mixedInMeanZero.exists_add_mem_mem_orthogonal z
  have h : y.val ∈ meanZero ⊓ mixedClosureᗮ :=
    ⟨y.property, fun v hv => hy (mixedInclusion ⟨v, hv⟩) hv⟩
  rw [← defectLine_sup_common] at h
  obtain ⟨v, hv, w, hw, he⟩ := Submodule.mem_sup.mp h
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
  exact ⟨m, hm, t, ⟨w, hw⟩, congrArg (m + ·) (Subtype.ext he.symm)⟩

/-- For an arbitrary representative the first term is its quotient norm squared.
Pairing with the defect is invariant under changing the representative by a mixed vector. -/
theorem quotient_mk_norm_loss (z : meanZero) :
    ‖Φ (mixedInMeanZero.mkQ z)‖ ^ 2 =
      ‖mixedInMeanZero.mkQ z‖ ^ 2 - inner ℝ z defect ^ 2 / (1 + ‖defect‖ ^ 2) := by
  obtain ⟨m, hm, t, w, rfl⟩ := exists_mixed_defect_common z
  let wZ : meanZero := ⟨w.val, w.property.1⟩
  have hm0 : mixedInMeanZero.mkQ m = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hm
  have hi : inner ℝ (m + (t • defect + wZ)) defect = t * ‖defect‖ ^ 2 := by
    rw [inner_add_left, defect_orthogonal m hm, zero_add, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, (real_inner_comm defect wZ).trans (defect_inner_common w),
      add_zero]
  have hE : limitEnergy = ‖defect‖ ^ 2 / (1 + ‖defect‖ ^ 2) :=
    (eq_div_iff (by positivity)).mpr energy_mul_one_add_defect
  rw [map_add, hm0, zero_add, hi, (quotient_norms_defect_add t w).1,
    (quotient_norms_defect_add t w).2, hE]
  field_simp [show 1 + ‖defect‖ ^ 2 ≠ 0 by positivity]
  ring

/-- The shortest representative gives the ambient-vector form of the norm loss. -/
theorem quotient_norm_loss_of_orthogonal (z : meanZero) (hz : z.val ∈ mixedClosureᗮ) :
    ‖Φ (mixedInMeanZero.mkQ z)‖ ^ 2 =
      ‖z‖ ^ 2 - inner ℝ z defect ^ 2 / (1 + ‖defect‖ ^ 2) := by
  have hz' : z ∈ mixedInMeanZeroᗮ := fun m hm => hz m.val hm
  rw [quotient_mk_norm_loss, norm_mk_orthogonalProjection,
    Submodule.starProjection_eq_self_iff.mpr hz']

/-- A class retains its norm precisely when its representatives are perpendicular to the defect. -/
theorem quotient_preserves_norm_iff (z : meanZero) :
    ‖Φ (mixedInMeanZero.mkQ z)‖ = ‖mixedInMeanZero.mkQ z‖ ↔ inner ℝ z defect = 0 := by
  have h := quotient_mk_norm_loss z
  constructor
  · intro he
    rw [he] at h
    have hn : inner ℝ z defect ^ 2 / (1 + ‖defect‖ ^ 2) = 0 := by linarith
    have hs : inner ℝ z defect ^ 2 = 0 :=
      (div_eq_zero_iff.mp hn).resolve_right (by positivity)
    simpa using hs
  · intro hz
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa [hz] using h

/-- Exact norm multiplier on the whole centered boundary line. -/
theorem quotient_boundary_norm (a : ℝ) :
    ‖Φ (boundary a)‖ = Real.sqrt (1 - limitEnergy) * ‖boundary a‖ := by
  have he : ‖Φ (mixedInMeanZero.mkQ defect)‖ ^ 2 = limitEnergy := by
    simpa only [boundary_apply, one_smul] using transported_boundary_one_norm_sq
  have h : ‖Φ (mixedInMeanZero.mkQ defect)‖ =
      Real.sqrt (1 - limitEnergy) * ‖mixedInMeanZero.mkQ defect‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [he, mul_pow, Real.sq_sqrt one_sub_limitEnergy_pos.le,
      show ‖mixedInMeanZero.mkQ defect‖ = ‖defect‖ from norm_defect_class]
    nlinarith only [energy_mul_one_add_defect]
  simp only [boundary_apply, map_smul, norm_smul, h]
  ring

private theorem quotient_inverse_bound (q : BoundaryTarget) :
    ‖q‖ ≤ Real.sqrt (1 + ‖defect‖ ^ 2) * ‖Φ q‖ := by
  obtain ⟨z, rfl⟩ := mixedInMeanZero.mkQ_surjective q
  obtain ⟨m, hm, t, w, rfl⟩ := exists_mixed_defect_common z
  rw [map_add, show mixedInMeanZero.mkQ m = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hm,
    zero_add]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), (quotient_norms_defect_add t w).1,
    (quotient_norms_defect_add t w).2]
  have he := congrArg (fun a : ℝ => t ^ 2 * a) energy_mul_one_add_defect
  nlinarith only [he, mul_nonneg (sq_nonneg ‖defect‖) (sq_nonneg ‖w‖)]

/-- In the nonzero-defect case the inverse attains its operator norm on the image of the defect. -/
theorem quotient_inverse_opNorm_of_defect_ne_zero (hd : defect ≠ 0) :
    ‖(Φ).symm.toContinuousLinearMap‖ = Real.sqrt (1 + ‖defect‖ ^ 2) := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro y
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
      quotient_inverse_bound ((Φ).symm y)
  · let q := mixedInMeanZero.mkQ defect
    have hn : ‖q‖ = ‖defect‖ := norm_defect_class
    have he : ‖Φ q‖ ^ 2 = limitEnergy := by
      simpa only [boundary_apply, one_smul] using transported_boundary_one_norm_sq
    have hs : Real.sqrt (1 + ‖defect‖ ^ 2) * ‖Φ q‖ = ‖q‖ := by
      apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
      rw [mul_pow, Real.sq_sqrt (by positivity), he, hn, mul_comm]
      exact energy_mul_one_add_defect
    have hp : 0 < ‖Φ q‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) ?_
      intro hz
      rw [← hz, mul_zero, hn] at hs
      exact (norm_pos_iff.mpr hd).ne hs
    have hle := (Φ).symm.toContinuousLinearMap.le_opNorm (Φ q)
    change ‖(Φ).symm (Φ q)‖ ≤ _ at hle
    rw [ContinuousLinearEquiv.symm_apply_apply, ← hs] at hle
    exact le_of_not_gt (fun hlt => (not_lt_of_ge hle) (mul_lt_mul_of_pos_right hlt hp))

/-- The inclusion-induced equivalence is an isometry exactly when the centered defect vanishes. -/
theorem quotient_isometry_iff_defect_zero : Isometry Φ ↔ defect = 0 := by
  constructor
  · intro h
    have hn := (AddMonoidHomClass.isometry_iff_norm Φ).mp h (mixedInMeanZero.mkQ defect)
    exact inner_self_eq_zero.mp ((quotient_preserves_norm_iff defect).mp hn)
  · intro hd
    apply (AddMonoidHomClass.isometry_iff_norm Φ).mpr
    intro q
    obtain ⟨z, rfl⟩ := mixedInMeanZero.mkQ_surjective q
    exact (quotient_preserves_norm_iff z).mpr (by rw [hd, inner_zero_right])

private theorem defect_zero_iff_one_mem : defect = 0 ↔ hilbertOne ∈ closedSpace := by
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo]
  exact ⟨fun h => sub_eq_zero.mp (congrArg Subtype.val h),
    fun h => Subtype.ext (sub_eq_zero.mpr h)⟩

/-- Equivalent arithmetic criterion in the ambient Pareto space. -/
theorem quotient_isometry_iff_energy_zero : Isometry Φ ↔ limitEnergy = 0 :=
  quotient_isometry_iff_defect_zero.trans
    (defect_zero_iff_one_mem.trans limitEnergy_zero_iff_mem.symm)

/-- When the defect vanishes the Pareto density theorem makes the two quotient spaces trivial. -/
theorem quotient_inverse_opNorm_of_defect_zero (hd : defect = 0) :
    ‖(Φ).symm.toContinuousLinearMap‖ = 0 := by
  let _ : Subsingleton BoundaryTarget :=
    boundaryTarget_subsingleton_iff_one_mem.mpr (defect_zero_iff_one_mem.mp hd)
  have he : (Φ).symm.toContinuousLinearMap = 0 :=
    ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _
  rw [he, norm_zero]

/-- Moving the domain to any support-stage target leaves precisely the same isometry criterion. -/
theorem stage_comparison_isometry_iff (S : Submodule ℝ mixedClosure) :
    Isometry (Φ ∘ Stage.targetIsometryEquiv S) ↔ defect = 0 := by
  constructor
  · intro h
    apply quotient_isometry_iff_defect_zero.mp
    simpa only [Function.comp_def, LinearIsometryEquiv.apply_symm_apply] using
      h.comp (Stage.targetIsometryEquiv S).symm.isometry
  · intro hd
    exact (quotient_isometry_iff_defect_zero.mpr hd).comp (Stage.targetIsometryEquiv S).isometry

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
