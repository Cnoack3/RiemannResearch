import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# The scalar relating the projected constant to the normalized screened packet

Pairing the scalar equation with the projected constant gives its reciprocal
squared norm. Pairing with the normalized screened packet gives its squared norm.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The normalized screened packet is a positive multiple of the projected constant. -/
theorem normalizedScreenedTwo_eq_norm_sq_smul_limitProjection :
    normalizedScreenedTwo = (‖normalizedScreenedTwo‖ ^ 2) • limitProjection := by
  have hu : 0 < ‖normalizedScreenedTwo‖ := zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo
  rw [limitProjection_eq_inv_norm_sq_smul_screenedTwo, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 hu.ne'), one_smul]

/-- Pairing the scalar equation with the projected constant determines the coefficient. -/
theorem normalizedScreenedTwo_projection_scalar {c : ℝ}
    (hc : normalizedScreenedTwo = c • limitProjection) :
    0 < c ∧ 1 = c * ‖limitProjection‖ ^ 2 ∧
      c = 1 / ‖limitProjection‖ ^ 2 ∧ c = ‖normalizedScreenedTwo‖ ^ 2 := by
  have hpair : 1 = c * ‖limitProjection‖ ^ 2 := calc
    1 = inner ℝ limitProjection normalizedScreenedTwo :=
      limitProjection_inner_normalizedScreenedTwo.symm
    _ = inner ℝ limitProjection (c • limitProjection) := congrArg (inner ℝ limitProjection) hc
    _ = c * ‖limitProjection‖ ^ 2 := by rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hp : ‖limitProjection‖ ^ 2 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hpair
    exact one_ne_zero hpair
  have hcNorm : c = ‖normalizedScreenedTwo‖ ^ 2 := by
    have h := congrArg (fun v : ThresholdHilbert => inner ℝ v normalizedScreenedTwo) hc
    simpa only [real_inner_self_eq_norm_sq, real_inner_smul_left,
      limitProjection_inner_normalizedScreenedTwo, mul_one] using h.symm
  have hu : 0 < ‖normalizedScreenedTwo‖ := zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo
  refine ⟨?_, hpair, (eq_div_iff hp).mpr hpair.symm, hcNorm⟩
  rw [hcNorm]
  exact sq_pos_of_pos hu

/-- The projected pair attains Cauchy–Schwarz unconditionally. -/
theorem limitProjection_normalizedScreenedTwo_cauchySchwarz_eq :
    |inner ℝ limitProjection normalizedScreenedTwo| =
      ‖limitProjection‖ * ‖normalizedScreenedTwo‖ := by
  have hu : 0 < ‖normalizedScreenedTwo‖ := zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo
  rw [limitProjection_inner_normalizedScreenedTwo, abs_one,
    limitProjection_eq_inv_norm_sq_smul_screenedTwo, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hu)), mul_assoc, ← pow_two,
    inv_mul_cancel₀ (pow_ne_zero 2 hu.ne')]

/-- The residual of the ambient constant is orthogonal to the screened packet. -/
theorem limitResidual_inner_normalizedScreenedTwo :
    inner ℝ limitResidual normalizedScreenedTwo = 0 := by
  change inner ℝ (hilbertOne - limitProjection) normalizedScreenedTwo = 0
  rw [inner_sub_left, real_inner_comm normalizedScreenedTwo hilbertOne,
    normalizedScreenedTwo_mean, limitProjection_inner_normalizedScreenedTwo, sub_self]

/-- Cancelling the positive scalar in the residual pairing recovers orthogonality
to the projected constant itself. -/
theorem limitResidual_inner_limitProjection : inner ℝ limitResidual limitProjection = 0 := by
  have hu := normalizedScreenedTwo_eq_norm_sq_smul_limitProjection
  have hpos := (normalizedScreenedTwo_projection_scalar hu).1
  have h := limitResidual_inner_normalizedScreenedTwo
  rw [hu, real_inner_smul_right] at h
  exact (mul_eq_zero.mp h).resolve_left hpos.ne'

/-- The reciprocal squared projection norm specifies exactly the scalar giving the packet. -/
theorem normalizedScreenedTwo_eq_smul_limitProjection_iff {c : ℝ} :
    normalizedScreenedTwo = c • limitProjection ↔ c = 1 / ‖limitProjection‖ ^ 2 := by
  constructor
  · intro hu
    exact (normalizedScreenedTwo_projection_scalar hu).2.2.1
  · intro hc
    have hu := normalizedScreenedTwo_eq_norm_sq_smul_limitProjection
    rw [hc, ← (normalizedScreenedTwo_projection_scalar hu).2.2.1]
    exact hu

/-- Orthogonality lets the projected constant replace the ambient constant in this pairing. -/
theorem scaled_limitProjection_abs_inner_one {c : ℝ} (hc : c = 1 / ‖limitProjection‖ ^ 2) :
    |inner ℝ hilbertOne (c • limitProjection)| = 1 := by
  have hu := normalizedScreenedTwo_eq_smul_limitProjection_iff.mpr hc
  obtain ⟨hpos, hpair, _, _⟩ := normalizedScreenedTwo_projection_scalar hu
  have horth := limitResidual_inner_normalizedScreenedTwo
  change inner ℝ (hilbertOne - limitProjection) normalizedScreenedTwo = 0 at horth
  rw [hu, inner_sub_left, sub_eq_zero] at horth
  calc
    |inner ℝ hilbertOne (c • limitProjection)| =
        |inner ℝ limitProjection (c • limitProjection)| := congrArg abs horth
    _ = c * ‖limitProjection‖ ^ 2 := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq,
        abs_of_nonneg (mul_nonneg hpos.le (sq_nonneg _))]
    _ = 1 := hpair.symm

/-- The product of the ambient norms in Cauchy–Schwarz is the square root of the scalar. -/
theorem scaled_limitProjection_ambient_norm_product {c : ℝ}
    (hc : c = 1 / ‖limitProjection‖ ^ 2) :
    ‖hilbertOne‖ * ‖c • limitProjection‖ = Real.sqrt c := by
  have hu := normalizedScreenedTwo_eq_smul_limitProjection_iff.mpr hc
  obtain ⟨hpos, _, _, hsq⟩ := normalizedScreenedTwo_projection_scalar hu
  have hOne := congrArg Real.sqrt hilbertOne_norm_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] at hOne
  calc
    ‖hilbertOne‖ * ‖c • limitProjection‖ = c * ‖limitProjection‖ := by
      rw [hOne, one_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    _ = ‖normalizedScreenedTwo‖ := by rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    _ = Real.sqrt c := by rw [hsq, Real.sqrt_sq (norm_nonneg _)]

/-- The exact pairing gives the bound by one, and ambient Cauchy–Schwarz gives the bound by
the square root of the scalar. -/
theorem scaled_limitProjection_pairing_bounds {c : ℝ} (hc : c = 1 / ‖limitProjection‖ ^ 2) :
    |inner ℝ hilbertOne (c • limitProjection)| ≤ 1 ∧ 1 ≤ Real.sqrt c := by
  have hpair := scaled_limitProjection_abs_inner_one hc
  refine ⟨hpair.le, ?_⟩
  calc
    1 = |inner ℝ hilbertOne (c • limitProjection)| := hpair.symm
    _ ≤ ‖hilbertOne‖ * ‖c • limitProjection‖ := abs_real_inner_le_norm _ _
    _ = Real.sqrt c := scaled_limitProjection_ambient_norm_product hc

/-- Attainment of the ambient norm product, a unit scalar, and coincidence of the three
vectors are equivalent. -/
theorem scaled_limitProjection_ambient_equality_iff {c : ℝ} (hc : c = 1 / ‖limitProjection‖ ^ 2) :
    (|inner ℝ hilbertOne (c • limitProjection)| = ‖hilbertOne‖ * ‖c • limitProjection‖ ↔
      c = 1) ∧
    (c = 1 ↔ normalizedScreenedTwo = hilbertOne ∧ hilbertOne = limitProjection) := by
  have hu := normalizedScreenedTwo_eq_smul_limitProjection_iff.mpr hc
  obtain ⟨hpos, _, _, hsq⟩ := normalizedScreenedTwo_projection_scalar hu
  constructor
  · rw [scaled_limitProjection_abs_inner_one hc, scaled_limitProjection_ambient_norm_product hc]
    constructor
    · intro h
      calc
        c = (Real.sqrt c) ^ 2 := (Real.sq_sqrt hpos.le).symm
        _ = 1 := by rw [← h, one_pow]
    · rintro rfl
      exact Real.sqrt_one.symm
  · constructor
    · intro h
      have hp : normalizedScreenedTwo = limitProjection := by simpa only [h, one_smul] using hu
      have he := normalizedScreenedTwo_eq_limitProjection_iff.mp hp
      exact ⟨he, he.symm.trans hp⟩
    · rintro ⟨he, _⟩
      rw [hsq, he, hilbertOne_norm_sq]

end RiemannResearch.RH.Pareto.PrimePowerSchur
