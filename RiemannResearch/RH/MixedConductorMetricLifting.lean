import RiemannResearch.RH.MixedConductorContractiveSection
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.ParetoMellinCenteredProduct
import RiemannResearch.RH.ParetoBeurlingMellinObstruction
import RiemannResearch.RH.RamanujanSchurLogZero
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Metric lifting for the legal Pareto mean

Helemskii, *Metric freedom and projectivity for classical and quantum normed modules*,
Definition 1.4 and Example 2.7 (https://arxiv.org/abs/1112.5750), formulates
norm-preserving lifting using surjections of closed unit balls. We calculate the image
of the ball for the real Pareto mean and its normalized scalar quotient directly.

Bagchi, Theorem 1 (https://arxiv.org/abs/math/0607733), identifies membership of the
constant in the legal closure with RH. The RH-to-approximation direction of the
published theorem is an explicit input to the corresponding Lean equivalence below.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- Full screening gives the sharp norm lower bound in each mean fiber. -/
theorem legalPacketMean_fiber_bound (v : closedSpace) :
    |legalPacketMean v| * ‖normalizedScreenedTwo‖ ≤ ‖v‖ := by
  have hv := fullScreening_eq_mean_smul v.property
  have hn : ‖fullScreening (v : ThresholdHilbert)‖ ≤ ‖(v : ThresholdHilbert)‖ := by
    change ‖(v : ThresholdHilbert) - mixedClosure.starProjection v‖ ≤ _
    rw [← Submodule.starProjection_orthogonal_val]
    exact mixedClosure.orthogonal.norm_orthogonalProjectionOnto_apply_le _
  rw [hv, norm_smul, Real.norm_eq_abs] at hn
  exact hn

/-- The image of the legal closed unit ball with its two endpoints included. -/
theorem legalPacketMean_unitBall_image (a : ℝ) :
    (∃ v : closedSpace, legalPacketMean v = a ∧ ‖v‖ ≤ 1) ↔
      |a| ≤ 1 / ‖normalizedScreenedTwo‖ := by
  have hu : 0 < ‖normalizedScreenedTwo‖ := lt_of_lt_of_le zero_lt_one
    one_le_norm_normalizedScreenedTwo
  rw [le_div_iff₀ hu]
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact (legalPacketMean_fiber_bound v).trans hv
  · intro ha
    refine ⟨screenedMeanSection a, ?_, ?_⟩
    · exact congrArg (fun f : ℝ →L[ℝ] ℝ => f a) legalPacketMean_comp_screenedMeanSection
    · change ‖a • normalizedScreenedTwo‖ ≤ 1
      rwa [norm_smul, Real.norm_eq_abs]

/-- With the quotient normalization the real scalar line admits an isometric
section, and the quotient map is contractive. -/
theorem normalized_legalPacketMean_isometric_section :
    ∃ s : ℝ →L[ℝ] closedSpace,
      (‖normalizedScreenedTwo‖ • legalPacketMean).comp s = ContinuousLinearMap.id ℝ ℝ ∧
      (∀ a : ℝ, ‖s a‖ = ‖a‖) ∧ ‖‖normalizedScreenedTwo‖ • legalPacketMean‖ ≤ 1 := by
  let c := ‖normalizedScreenedTwo‖
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one one_le_norm_normalizedScreenedTwo
  refine ⟨c⁻¹ • screenedMeanSection, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro a
    change c * legalPacketMean (c⁻¹ • screenedMeanSection a) = a
    have ha := congrArg (fun f : ℝ →L[ℝ] ℝ => f a) legalPacketMean_comp_screenedMeanSection
    change legalPacketMean (screenedMeanSection a) = a at ha
    rw [map_smul, ha, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  · intro a
    change ‖c⁻¹ • (a • normalizedScreenedTwo)‖ = ‖a‖
    rw [norm_smul, norm_smul, Real.norm_eq_abs c⁻¹, abs_of_pos (inv_pos.mpr hc)]
    change c⁻¹ * (‖a‖ * c) = ‖a‖
    field_simp
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖c * legalPacketMean v‖ ≤ 1 * ‖v‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hc, mul_comm c, one_mul]
    exact legalPacketMean_fiber_bound v

/-- A concrete unconditional section for the unscaled mean, using the complete
period-5040 estimate for its squared operator norm. -/
theorem exists_legalMeanSection_period5040 :
    ∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ^ 2 < (1000 : ℝ) / 961 := by
  refine ⟨screenedMeanSection, legalPacketMean_comp_screenedMeanSection, ?_⟩
  have h := legalMeanSection_norm_sq screenedMeanSection legalPacketMean_comp_screenedMeanSection
  change ‖screenedMeanSection‖ ^ 2 = ‖normalizedScreenedTwo‖ ^ 2 +
    ‖(1 : ℝ) • normalizedScreenedTwo - normalizedScreenedTwo‖ ^ 2 at h
  simpa only [h, one_smul, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    using normalizedScreenedTwo_norm_sq_lt_period5040

/-- A contractive lift of the physical unit implies RH with no analytic hypothesis. -/
theorem riemannHypothesis_of_legalMeanSection {s : ℝ →L[ℝ] closedSpace}
    (hs : legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ) (hcontract : ‖s‖ ≤ 1) :
    RiemannHypothesis := by
  have h := screenedPrimeClosure_eq_constantLine_iff_contractive_section.mpr ⟨s, hs, hcontract⟩
  have hw : hilbertOne ∈ screenedPrimeClosure := by
    rw [h]
    exact Submodule.subset_span (Set.mem_singleton _)
  exact riemannHypothesis_of_normalizedScreenedTwo
    (one_mem_closedSpace_iff_normalizedScreenedTwo.mp (screenedPrimeClosure_le_closedSpace hw))

/-- The literature-to-Lean interface for the converse is displayed as a hypothesis. -/
theorem exists_contractive_legalMeanSection_iff_riemannHypothesis
    (hBD : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    (∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ 1) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨s, hs, hn⟩
    exact riemannHypothesis_of_legalMeanSection hs hn
  · intro hRH
    have hv := BaezDuarte.naturalApproximation_iff_one_mem.mp (hBD hRH)
    apply screenedPrimeClosure_eq_constantLine_iff_contractive_section.mp
    rw [screenedPrimeClosure_eq_span_two, one_mem_closedSpace_iff_normalizedScreenedTwo.mp hv]

open RiemannResearch.RH.ParetoBeurlingMellinObstruction in
/-- Every finite set of distinct right-half-plane zeros imposes a cost on any
section of the actual mean. This finite inequality follows from the repository's
Mellin Gram identity. Burnol, Theorem 1.2 (https://arxiv.org/abs/math/9910055),
gives the related infinite product for projection onto the continuous Nyman space. -/
theorem legalMeanSection_finite_zero_product {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (hinj : Function.Injective z) (hz : ∀ i, riemannZeta (z i) = 0)
    (hre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hne : ∀ i, z i ≠ 1)
    (s : ℝ →L[ℝ] closedSpace)
    (hs : legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ) :
    1 ≤ mellinCenteredProduct z 1 * ‖s‖ ^ 2 := by
  classical
  have hp : limitProjection ∈ normalizedResidueClosure := by
    rw [← RamanujanSchurLogZero.closedSpace_eq_normalizedResidueClosure]
    exact closedSpace.starProjection_apply_mem hilbertOne
  have hsig (i : ι) : paretoMellin limitResidual (z i) = 1 / z i :=
    paretoMellin_normalizedResidue_error_identity
      (z i) (hre i) (hne i) (hz i) limitProjection hp
  have hgram := finiteMellinKernel_inverse_completion limitResidual z hre
    ((mellinCauchyGram_det_ne_zero_iff_injective z hre).mpr hinj)
  have hcap : mellinInverseCapacity z (fun i => paretoMellin limitResidual (z i)) ≤
      ‖limitResidual‖ ^ 2 := by
    rw [hgram]
    exact le_add_of_nonneg_right (MeasureTheory.integral_nonneg (fun _ => sq_nonneg _))
  simp_rw [hsig] at hcap
  have hprod := mellinInverseCapacity_centered_product z 1 hre (by norm_num) hinj
  simp at hprod
  norm_num at hprod
  simp only [one_div] at hcap
  rw [hprod] at hcap
  change 1 - mellinCenteredProduct z 1 ≤ limitEnergy at hcap
  have hscale : 1 - limitEnergy ≤ mellinCenteredProduct z 1 := by linarith
  have hmin : ‖normalizedScreenedTwo‖ ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [legalMeanSection_norm_sq s hs]
    exact le_add_of_nonneg_right (sq_nonneg _)
  calc
    1 = (1 - limitEnergy) * ‖normalizedScreenedTwo‖ ^ 2 :=
      normalizedScreenedTwo_energy_product.symm
    _ ≤ mellinCenteredProduct z 1 * ‖normalizedScreenedTwo‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hscale (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hmin (mellinCenteredProduct_nonneg z 1)

end RiemannResearch.RH.Pareto.PrimePowerSchur
