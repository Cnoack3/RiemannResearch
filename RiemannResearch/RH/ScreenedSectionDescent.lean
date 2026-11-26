import RiemannResearch.RH.PrimeSupportParityDescent
import RiemannResearch.RH.MixedParityDigammaParseval
import RiemannResearch.RH.PhysicalHeadInfiniteBoundary
import RiemannResearch.RH.ParetoHeadMeanEnergy

/-!
# The screened mean section along the support and physical-head descents

The support residuals converge to the legal section at one. Pairing this
section with a legal exact head computes the surviving defect as a centered
tail pairing. Sublinear physical-head cost then reduces unit norm to a
cofinal bound on conditional tail variance. The arithmetic bound is open.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.ScreenedSectionDescent
open CoefficientStabilization AffineHeadTower MixedConductorBasis

/-- The representative obtained by removing the mixed component through support depth n. -/
def supportResidual (n : ℕ) : ThresholdHilbert :=
  (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 -
    (((supportSpace n).starProjection parityMixedProjection : mixedClosure) : ThresholdHilbert)

theorem supportResidual_split (n : ℕ) :
    supportResidual n = normalizedScreenedTwo +
      ((parityMixedProjection - (supportSpace n).starProjection parityMixedProjection :
        mixedClosure) : ThresholdHilbert) := by
  have hu := CenteredMeanSnake.normalizedScreenedTwo_eq_projected_packet
  rw [Submodule.starProjection_orthogonal_val, smul_sub] at hu
  change (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - _ = normalizedScreenedTwo +
    (mixedClosure.starProjection ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2) - _)
  rw [hu, map_smul]
  abel

/-- The limit of the actual support residuals is the value of the legal section at one. -/
theorem supportResidual_tendsto_section :
    Tendsto supportResidual atTop (𝓝 ((screenedMeanSection 1 : closedSpace) : ThresholdHilbert)) := by
  have hp := tendsto_sum_supportLayer_projection parityMixedProjection
  simp only [sum_supportLayer_projection] at hp
  have ht := mixedClosure.subtypeL.continuous.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := parityMixedProjection)).sub hp)
  change Tendsto (fun n => supportResidual n) atTop (𝓝 ((1 : ℝ) • normalizedScreenedTwo))
  simpa only [supportResidual_split, Function.comp_def, Submodule.subtypeL_apply,
    sub_self, Submodule.coe_zero, add_zero, one_smul] using
    (tendsto_const_nhds (x := normalizedScreenedTwo)).add ht

/-- The squared error of the representative is exactly the squared quotient norm. -/
theorem supportResidual_error (n : ℕ) :
    ‖supportResidual n - hilbertOne‖^2 = ‖parityQuotientClass n‖^2 := by
  let t : mixedClosure := parityMixedProjection - (supportSpace n).starProjection parityMixedProjection
  have ho : inner ℝ (normalizedScreenedTwo - hilbertOne) (t : ThresholdHilbert) = 0 :=
    (real_inner_comm _ _).trans (CenteredMeanSnake.screenedTwo_sub_one_mem_orthogonals.2 _ t.property)
  rw [supportResidual_split, parityQuotientClass_norm_sq, CenteredMeanSnake.boundary_norm]
  change ‖normalizedScreenedTwo + (t : ThresholdHilbert) - hilbertOne‖^2 =
    ‖normalizedScreenedTwo - hilbertOne‖^2 + ‖t‖^2
  rw [show normalizedScreenedTwo + (t : ThresholdHilbert) - hilbertOne =
    (normalizedScreenedTwo - hilbertOne) + (t : ThresholdHilbert) by abel,
    norm_add_sq_real, ho]
  change ‖normalizedScreenedTwo - hilbertOne‖^2 + 2*0 + ‖t‖^2 = _
  ring

private theorem unit_inner_iff_boundary :
    inner ℝ normalizedScreenedTwo normalizedScreenedTwo = 1 ↔ CenteredMeanSnake.boundary = 0 := by
  have he : ‖CenteredMeanSnake.boundary‖^2 =
      inner ℝ normalizedScreenedTwo normalizedScreenedTwo - 1 := by
    rw [real_inner_self_eq_norm_sq]
    exact CenteredMeanSnake.boundary_norm_sq
  constructor
  · intro h
    rw [h, sub_self] at he
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  · intro hb
    rw [hb, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    linarith

/-- Section 8 of the descent: a fixed fractional contraction on arbitrarily
late blocks is equivalent to the unit self-pairing. -/
theorem inner_self_eq_one_iff_support_contraction {c : ℝ} (hc₀ : 0 < c) (hc : c < 1) :
    inner ℝ normalizedScreenedTwo normalizedScreenedTwo = 1 ↔
      ∃ᶠ n in atTop, ∃ m : ℕ, n ≤ m ∧
        ‖supportResidual m - hilbertOne‖^2 ≤ c * ‖supportResidual n - hilbertOne‖^2 := by
  simp only [supportResidual_error]
  exact unit_inner_iff_boundary.trans (boundary_eq_zero_iff_frequent_support_contraction hc₀ hc)

/-- Pareto conditional variance above site N. The retained vector agrees on the
head and equals the conditional mean on the tail, whose mass is 1/(N+1). -/
def tailVariance (N : ℕ) (f : ThresholdHilbert) : ℝ :=
  ((N : ℝ) + 1) * ‖f - paretoHeadMeanMinimizer N f‖ ^ 2

private theorem tailVariance_one (N : ℕ) : tailVariance N hilbertOne = 0 := by
  have hm : paretoHeadMean N hilbertOne = 1 - 1 / ((N : ℝ) + 1) := by
    simpa [paretoHeadMean, hilbertGibbs_one_physical] using paretoWeight_partial_sum N
  have hc : ((N : ℝ) + 1) *
      (inner ℝ hilbertOne hilbertOne - paretoHeadMean N hilbertOne) = 1 := by
    rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq, hm]
    field_simp
    ring
  have he : paretoHeadMeanMinimizer N hilbertOne = hilbertOne := by
    rw [paretoHeadMeanMinimizer, hc, one_smul]
    simp only [paretoHead, hilbertGibbs_one_physical, one_smul, paretoTail]
    abel
  simp [tailVariance, he]

/-- The signed covariance numerator for every legal mean-one exact head. -/
theorem exactHead_tail_pairing {N : ℕ} {v : ThresholdHilbert} (hv : v ∈ fiber N) :
    inner ℝ (v - hilbertOne)
      (normalizedScreenedTwo - paretoHeadMeanMinimizer N normalizedScreenedTwo) =
      inner ℝ normalizedScreenedTwo normalizedScreenedTwo - 1 := by
  obtain ⟨hV, hmean, hhead⟩ := hv
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  have hm : v - normalizedScreenedTwo ∈ mixedClosure :=
    (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
      ⟨closedSpace.sub_mem hV hu.1, by rw [inner_sub_left, hmean, normalizedScreenedTwo_mean, sub_self]⟩
  have ho := hu.2 _ hm
  rw [inner_sub_left] at ho
  have hz : ∀ i < N, hilbertGibbsPhysical (v - hilbertOne) i = 0 := by
    intro i hi
    rw [hilbertGibbsPhysical_eq, ← physicalEvaluationCLM_apply, map_sub, hhead i hi,
      physicalEvaluationCLM_apply, hilbertOne_sequence]
    simp [zeroAnchor]
  have hzmean : inner ℝ (v - hilbertOne) hilbertOne = 0 := by
    rw [inner_sub_left, hmean, real_inner_self_eq_norm_sq, hilbertOne_norm_sq, sub_self]
  have hh : inner ℝ (v - hilbertOne) (paretoHead N normalizedScreenedTwo) = 0 := by
    rw [paretoHead_inner]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hz i (Finset.mem_range.mp hi), zero_mul, mul_zero]
  have hhm : paretoHeadMean N (v - hilbertOne) = 0 := by
    unfold paretoHeadMean
    apply Finset.sum_eq_zero
    intro i hi
    rw [hz i (Finset.mem_range.mp hi), mul_zero]
  have h_one : inner ℝ hilbertOne normalizedScreenedTwo = 1 :=
    (real_inner_comm _ _).trans normalizedScreenedTwo_mean
  rw [inner_sub_right, paretoHeadMeanMinimizer, inner_add_right, real_inner_smul_right,
    hh, paretoTail_inner, hzmean, hhm, sub_self, mul_zero, add_zero, sub_zero,
    inner_sub_left, h_one]
  linarith

theorem patch_tailVariance_bound (N : ℕ) :
    (inner ℝ normalizedScreenedTwo normalizedScreenedTwo - 1)^2 ≤
      (‖patch N - hilbertOne‖^2 / ((N : ℝ) + 1)) * tailVariance N normalizedScreenedTwo := by
  have h := real_inner_le_norm (patch N - hilbertOne)
    (normalizedScreenedTwo - paretoHeadMeanMinimizer N normalizedScreenedTwo)
  rw [exactHead_tail_pairing (patch_spec N).1] at h
  have hnon : 0 ≤ inner ℝ normalizedScreenedTwo normalizedScreenedTwo - 1 := by
    rw [real_inner_self_eq_norm_sq, ← CenteredMeanSnake.boundary_norm_sq]
    exact sq_nonneg _
  have hs := pow_le_pow_left₀ hnon h 2
  rw [mul_pow] at hs
  unfold tailVariance
  have hn : (N : ℝ) + 1 ≠ 0 := by positivity
  simpa only [div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc, inv_mul_cancel_left₀ hn] using hs

/-- Infinite descent closes the scalar goal exactly when the conditional
variances stay bounded along some unbounded sequence of physical heads. -/
theorem inner_self_eq_one_iff_cofinal_tailVariance :
    inner ℝ normalizedScreenedTwo normalizedScreenedTwo = 1 ↔
      ∃ C : ℝ, ∀ k : ℕ, ∃ n ≥ k, tailVariance n normalizedScreenedTwo ≤ C := by
  constructor
  · intro h
    have hu := CenteredMeanSnake.boundary_eq_zero_iff_screened.mp (unit_inner_iff_boundary.mp h)
    exact ⟨0, fun k => ⟨k, le_rfl, by rw [hu, tailVariance_one]⟩⟩
  · rintro ⟨C, hC⟩
    by_contra h
    let gap := (inner ℝ normalizedScreenedTwo normalizedScreenedTwo - 1)^2
    have hg : 0 < gap := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
    have hK : 0 < |C| + 1 := by positivity
    obtain ⟨k, hk⟩ := eventually_atTop.1 ((tendsto_order.mp patch_error_sublinear).2
      (gap / (|C| + 1)) (div_pos hg hK))
    obtain ⟨n, hn, hvar⟩ := hC (max k 1)
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hr := hk n (le_trans (le_max_left _ _) hn)
    have hrate : ‖patch n - hilbertOne‖^2 / ((n : ℝ) + 1) < gap / (|C| + 1) :=
      lt_of_le_of_lt (div_le_div_of_nonneg_left (sq_nonneg _) hnpos (by linarith)) hr
    have hbound : gap ≤ ‖patch n - hilbertOne‖^2 / ((n : ℝ) + 1) * (|C| + 1) :=
      (patch_tailVariance_bound n).trans (mul_le_mul_of_nonneg_left
        (hvar.trans (by linarith [le_abs_self C])) (by positivity))
    exact (not_lt_of_ge hbound) ((lt_div_iff₀ hK).mp hrate)

/-- The unnormalized signed digamma coefficients and the section account for
all of the parity energy. -/
theorem digamma_section_energy :
    (∑' q : Index, (DigammaParseval.digammaRow q 2)^2) +
      (Real.log 2)^2 * inner ℝ normalizedScreenedTwo normalizedScreenedTwo = Real.log 2 := by
  rw [DigammaParseval.hasSum_parity_energy.tsum_eq, full_mixed_capture_eq_limitEnergy,
    real_inner_self_eq_norm_sq, normalizedScreenedTwo_norm_sq]
  ring

/-- The scalar digamma endpoint and the physical-head test detect the same section. -/
theorem digamma_saturation_iff_cofinal_tailVariance :
    (∑' q : Index, (DigammaParseval.digammaRow q 2)^2) = Real.log 2 - (Real.log 2)^2 ↔
      ∃ C : ℝ, ∀ k : ℕ, ∃ n ≥ k, tailVariance n normalizedScreenedTwo ≤ C :=
  DigammaParseval.parity_endpoint_iff_one_mem.trans
    (CenteredMeanSnake.boundary_eq_zero_iff_one_mem.symm.trans
      (unit_inner_iff_boundary.symm.trans inner_self_eq_one_iff_cofinal_tailVariance))

theorem inner_self_eq_one_iff_rh :
    inner ℝ normalizedScreenedTwo normalizedScreenedTwo = 1 ↔ RiemannHypothesis :=
  unit_inner_iff_boundary.trans
    (PhysicalHeadStageAlgebra.productSnake_one_eq_zero_iff_centered_boundary.symm.trans
      PhysicalHeadStageAlgebra.productSnake_one_eq_zero_iff_rh)

end RiemannResearch.RH.Pareto.PrimePowerSchur.ScreenedSectionDescent
