import RiemannResearch.RH.MixedConductorContractiveSection
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.ParetoMellinCenteredProduct
import RiemannResearch.RH.ParetoBeurlingMellinObstruction
import RiemannResearch.RH.RamanujanSchurLogZero
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
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

/-- The canonical physical section attains the least possible operator norm. -/
theorem norm_screenedMeanSection : ‖screenedMeanSection‖ = ‖normalizedScreenedTwo‖ := by
  have h := legalMeanSection_norm_sq screenedMeanSection legalPacketMean_comp_screenedMeanSection
  change ‖screenedMeanSection‖ ^ 2 = ‖normalizedScreenedTwo‖ ^ 2 +
    ‖(1 : ℝ) • normalizedScreenedTwo - normalizedScreenedTwo‖ ^ 2 at h
  simp only [one_smul, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  exact le_antisymm ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h.le)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h.ge)

/-- Feasibility of any operator-norm budget for a right inverse of the unscaled mean. -/
theorem exists_legalMeanSection_norm_le_iff (B : ℝ) :
    (∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ B) ↔
      ‖normalizedScreenedTwo‖ ≤ B := by
  constructor
  · rintro ⟨s, hs, hB⟩
    apply le_trans _ hB
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [legalMeanSection_norm_sq s hs]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · intro hB
    exact ⟨screenedMeanSection, legalPacketMean_comp_screenedMeanSection,
      norm_screenedMeanSection.le.trans hB⟩

/-- Lifting the scalar one in the closed unit ball is exactly the operator section
condition, with the original physical normalization on both sides. -/
theorem exists_contractive_legalMeanSection_iff_unitBall_lifts_one :
    (∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ 1) ↔
      ∃ v : closedSpace, legalPacketMean v = 1 ∧ ‖v‖ ≤ 1 := by
  rw [exists_legalMeanSection_norm_le_iff, legalPacketMean_unitBall_image, abs_one,
    le_div_iff₀ (zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo), one_mul]

theorem exists_contractive_legalMeanSection_iff_limitEnergy_zero :
    (∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ 1) ↔ limitEnergy = 0 := by
  rw [exists_legalMeanSection_norm_le_iff, ← normalizedScreenedTwo_norm_eq_one_iff]
  exact ⟨fun h => le_antisymm h one_le_norm_normalizedScreenedTwo, fun h => h.le⟩

theorem screenedPrimeClosure_eq_constantLine_iff_limitEnergy_zero :
    screenedPrimeClosure = Submodule.span ℝ {hilbertOne} ↔ limitEnergy = 0 :=
  screenedPrimeClosure_eq_constantLine_iff_contractive_section.trans
    exists_contractive_legalMeanSection_iff_limitEnergy_zero

/-- A concrete unconditional section for the unscaled mean, using the complete
period-5040 estimate for its squared operator norm. -/
theorem exists_legalMeanSection_period5040 :
    ∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ^ 2 < (1000 : ℝ) / 961 := by
  refine ⟨screenedMeanSection, legalPacketMean_comp_screenedMeanSection, ?_⟩
  rw [norm_screenedMeanSection]
  exact normalizedScreenedTwo_norm_sq_lt_period5040

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

open MeasureTheory RiemannResearch.RH.ParetoBeurlingMellinObstruction in
/-- A finite family of right-hand zeros accounts for an explicit part of the physical
residual. The integral is the complete squared error left by its Mellin interpolant. -/
theorem limitEnergy_finite_zero_product_remainder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) (hinj : Function.Injective z) (hz : ∀ i, riemannZeta (z i) = 0)
    (hre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hne : ∀ i, z i ≠ 1) :
    limitEnergy = 1 - mellinCenteredProduct z 1 +
      ∫ x in Set.Ioi (1 : ℝ), ‖mellinWeightedStep limitResidual x -
        starRingEnd ℂ (finiteMellinKernel z
          (mellinInverseCoefficients z (fun i => (z i)⁻¹)) x)‖ ^ 2 := by
  have hp : limitProjection ∈ normalizedResidueClosure := by
    rw [← RamanujanSchurLogZero.closedSpace_eq_normalizedResidueClosure]
    exact closedSpace.starProjection_apply_mem hilbertOne
  have hsig (i : ι) : paretoMellin limitResidual (z i) = 1 / z i :=
    paretoMellin_normalizedResidue_error_identity
      (z i) (hre i) (hne i) (hz i) limitProjection hp
  have hgram := finiteMellinKernel_inverse_completion limitResidual z hre
    ((mellinCauchyGram_det_ne_zero_iff_injective z hre).mpr hinj)
  simp_rw [hsig, one_div] at hgram
  have hprod := mellinInverseCapacity_centered_product z 1 hre (by norm_num) hinj
  simp at hprod
  norm_num at hprod
  rw [hprod] at hgram
  exact hgram

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
  have hcap : 1 - mellinCenteredProduct z 1 ≤ limitEnergy := by
    rw [limitEnergy_finite_zero_product_remainder z hinj hz hre hne]
    exact le_add_of_nonneg_right (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
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

/-- Testing the certified physical section on a finite zero family gives a strict
rational lower bound independently of any density or approximation converse. -/
theorem finite_zero_product_gt_period5040 {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (hinj : Function.Injective z) (hz : ∀ i, riemannZeta (z i) = 0)
    (hre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hne : ∀ i, z i ≠ 1) :
    (961 : ℝ) / 1000 < mellinCenteredProduct z 1 := by
  obtain ⟨s, hs, hnorm⟩ := exists_legalMeanSection_period5040
  have hprod := legalMeanSection_finite_zero_product z hinj hz hre hne s hs
  by_contra! h
  have hupper := mul_le_mul_of_nonneg_right h (sq_nonneg ‖s‖)
  linarith only [hprod, hupper, hnorm]

private theorem singleton_mellinCenteredProduct (z : ℂ) :
    mellinCenteredProduct (fun _ : Fin 1 => z) 1 = ‖1 - z‖ ^ 2 / ‖z‖ ^ 2 := by
  simp [mellinCenteredProduct, norm_div, div_pow]

private theorem one_sub_complex_norm_sq (z : ℂ) :
    ‖1 - z‖ ^ 2 = ‖z‖ ^ 2 + 1 - 2 * z.re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im]
  ring

/-- One witnessed zero gives a positive lower bound on the physical section's
excess squared norm after clearing its nonzero denominator. -/
theorem legalMeanSection_single_zero_excess (z : ℂ) (hz : riemannZeta z = 0)
    (hre : (1 / 2 : ℝ) < z.re) (hne : z ≠ 1)
    (s : ℝ →L[ℝ] closedSpace) (hs : legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ) :
    2 * z.re - 1 ≤ ‖1 - z‖ ^ 2 * (‖s‖ ^ 2 - 1) := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hre
  have h := legalMeanSection_finite_zero_product (fun _ : Fin 1 => z)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hz) (fun _ => hre) (fun _ => hne) s hs
  rw [singleton_mellinCenteredProduct, div_mul_eq_mul_div,
    le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz0)), one_mul] at h
  rw [mul_sub, mul_one]
  linarith only [h, one_sub_complex_norm_sq z]

/-- Passing all finite zero-product tests at budget one is equivalent to RH.
The empty family passes automatically, and a singleton detects any right-hand zero. -/
theorem riemannHypothesis_iff_unit_finite_zero_products :
    RiemannHypothesis ↔ ∀ (n : ℕ) (z : Fin n → ℂ), Function.Injective z →
      (∀ i, riemannZeta (z i) = 0) → (∀ i, (1 / 2 : ℝ) < (z i).re) →
      (∀ i, z i ≠ 1) → 1 ≤ mellinCenteredProduct z 1 := by
  constructor
  · intro hRH n z _ hz hre _
    cases n with
    | zero => simp [mellinCenteredProduct]
    | succ n =>
      let i : Fin (n + 1) := 0
      have hlt : (z i).re < 1 :=
        lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h (hz i))
      exact ((RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mp hRH
        (z i) (hre i) hlt) (hz i)).elim
  · intro hall
    apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
    intro z hre hlt hz
    have hne : z ≠ 1 := by rintro rfl; norm_num at hlt
    have hz0 : z ≠ 0 := by rintro rfl; norm_num at hre
    have h := hall 1 (fun _ => z) (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hz)
      (fun _ => hre) (fun _ => hne)
    rw [singleton_mellinCenteredProduct, le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz0)),
      one_mul, one_sub_complex_norm_sq] at h
    linarith

end RiemannResearch.RH.Pareto.PrimePowerSchur
