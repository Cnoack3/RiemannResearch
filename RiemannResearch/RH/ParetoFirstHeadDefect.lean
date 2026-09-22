/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoAnnihilatorTail
import RiemannResearch.RH.CanonicalMobiusSingleHeadCapacity

/-!
# The first-head projection defect has necessarily heavy tails

Source: user-provided single-head duality handoff, Section 14, for the
projection residual and dilation method. No novelty is claimed. The vector below is the
actual orthogonal-projection residual for the first physical point target.
Its positive constant pairing is proved from dilation and the canonical
residual. It is not an arbitrary infinite common normal witness.
-/

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The actual projection defect of the first positive-coordinate indicator. -/
def firstHeadResidual : ThresholdHilbert :=
  finiteHeadIndicator 1 - closedSpace.starProjection (finiteHeadIndicator 1)

theorem firstHeadResidual_mem_orthogonal :
    firstHeadResidual ∈ closedSpaceᗮ :=
  Submodule.sub_starProjection_mem_orthogonal (finiteHeadIndicator 1)

/-- Self-adjointness of the complementary projection identifies its mean
with the strictly positive first pairing of the canonical residual. -/
theorem firstHeadResidual_inner_one :
    inner ℝ firstHeadResidual hilbertOne = residualHeadPairing 1 := by
  have hP : inner ℝ firstHeadResidual limitProjection = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp firstHeadResidual_mem_orthogonal _
      (closedSpace.starProjection_apply_mem hilbertOne)
  have heP : inner ℝ (closedSpace.starProjection (finiteHeadIndicator 1))
      limitResidual = 0 :=
    (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
      (closedSpace.starProjection_apply_mem (finiteHeadIndicator 1))
  have hone : hilbertOne = limitResidual + limitProjection := by
    unfold limitResidual
    abel
  calc
    inner ℝ firstHeadResidual hilbertOne =
        inner ℝ firstHeadResidual limitResidual := by
      rw [hone, inner_add_right, hP, add_zero]
    _ = inner ℝ (finiteHeadIndicator 1) limitResidual := by
      rw [firstHeadResidual, inner_sub_left, heP, sub_zero]
    _ = inner ℝ limitResidual (finiteHeadIndicator 1) := real_inner_comm _ _
    _ = residualHeadPairing 1 := finiteHead_residual_inner_eq_pairing 1

theorem firstHeadResidual_inner_one_pos (hpos : 0 < limitEnergy) :
    0 < inner ℝ firstHeadResidual hilbertOne := by
  rw [firstHeadResidual_inner_one]
  exact residualHeadPairing_pos 1 (by omega) hpos

/-- Failure of legal density with positive canonical residual forces heavy
tails for the distinct first-point projection residual as well. -/
theorem firstHeadResidual_normalized_tail_tendsto_atTop
    (hpos : 0 < limitEnergy) :
    Tendsto (fun N : ℕ => (N : ℝ) *
      ‖hilbertTailShift firstHeadResidual N‖^2) atTop atTop :=
  annihilator_normalized_tail_tendsto_atTop firstHeadResidual
    firstHeadResidual_mem_orthogonal
    (ne_of_gt (firstHeadResidual_inner_one_pos hpos))

/-- The hypothesis concerns one fixed, explicitly defined projection defect.
It is an open quantitative sufficient condition, not an established bound. -/
theorem riemannHypothesis_of_firstHeadResidual_frequently_bounded_tail
    (C : ℝ)
    (hbounded : ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * ‖hilbertTailShift firstHeadResidual N‖^2 ≤ C) :
    RiemannHypothesis := by
  by_contra hRH
  have hzero := annihilator_inner_one_eq_zero_of_frequently_bounded_tail
    firstHeadResidual firstHeadResidual_mem_orthogonal C hbounded
  have hpositive := firstHeadResidual_inner_one_pos (not_RH_limitEnergy_pos hRH)
  linarith

theorem firstHeadResidual_pairing_limitResidual :
    inner ℝ limitResidual firstHeadResidual =
      inner ℝ firstHeadResidual hilbertOne := by
  have ho : inner ℝ limitResidual
      (closedSpace.starProjection (finiteHeadIndicator 1)) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
      (closedSpace.starProjection_apply_mem (finiteHeadIndicator 1))
  rw [firstHeadResidual_inner_one, firstHeadResidual, inner_sub_right, ho, sub_zero,
    finiteHead_residual_inner_eq_pairing]

/-- The difference of the two defects is a compression of one half of the
dyadic dilation of the constant residual. Compression can only lower energy. -/
theorem firstHeadResidual_compressed_dilation_bound :
    ‖limitResidual - firstHeadResidual‖ ^ 2 ≤ limitEnergy / 2 := by
  let x : ThresholdHilbert := (1 / 2 : ℝ) • hilbertDilation 2 (by omega) limitResidual
  let y : ThresholdHilbert := limitResidual - firstHeadResidual
  have hd : hilbertDilation 2 (by omega) limitResidual =
      hilbertDilation 2 (by omega) hilbertOne -
        hilbertDilation 2 (by omega) limitProjection := by
    exact (hilbertDilationContinuous 2 (by omega)).map_sub hilbertOne limitProjection
  have he : finiteHeadIndicator 1 =
      hilbertOne - (1 / 2 : ℝ) • hilbertDilation 2 (by omega) hilbertOne := by
    simpa using finiteHeadIndicator_eq_dilation_difference 1
  have hdiff : x - y = limitProjection -
      closedSpace.starProjection (finiteHeadIndicator 1) -
      (1 / 2 : ℝ) • hilbertDilation 2 (by omega) limitProjection := by
    dsimp [x, y]
    rw [firstHeadResidual, hd, he, smul_sub]
    unfold limitResidual
    abel
  have hmem : x - y ∈ closedSpace := by
    rw [hdiff]
    exact closedSpace.sub_mem
      (closedSpace.sub_mem (closedSpace.starProjection_apply_mem hilbertOne)
        (closedSpace.starProjection_apply_mem (finiteHeadIndicator 1)))
      (closedSpace.smul_mem _ (closedSpace_dilation
        (closedSpace.starProjection_apply_mem hilbertOne) 2 (by omega)))
  have hy : y ∈ closedSpaceᗮ :=
    (closedSpaceᗮ).sub_mem limitResidual_mem_orthogonal firstHeadResidual_mem_orthogonal
  have ho : inner ℝ y (x - y) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp hy _ hmem
  have hsplit : ‖x‖ ^ 2 = ‖y‖ ^ 2 + ‖x - y‖ ^ 2 := by
    calc
      _ = ‖y + (x - y)‖ ^ 2 := by congr 2; abel
      _ = _ := by rw [norm_add_sq_real, ho]; ring
  have hxenergy : ‖x‖ ^ 2 = limitEnergy / 2 := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hilbertDilation_norm_sq]
    change (1 / 2 : ℝ) ^ 2 * (2 * ‖limitResidual‖ ^ 2) =
      ‖limitResidual‖ ^ 2 / 2
    ring
  change ‖y‖ ^ 2 ≤ limitEnergy / 2
  nlinarith [sq_nonneg ‖x - y‖]

/-- The exact inner-product consequence of the compressed dilation estimate. -/
theorem firstHeadResidual_energy_pairing_bound :
    limitEnergy ≤ 4 * inner ℝ firstHeadResidual hilbertOne -
      2 * ‖firstHeadResidual‖ ^ 2 := by
  have h := firstHeadResidual_compressed_dilation_bound
  rw [norm_sub_sq_real, firstHeadResidual_pairing_limitResidual] at h
  change limitEnergy - 2 * inner ℝ firstHeadResidual hilbertOne +
    ‖firstHeadResidual‖ ^ 2 ≤ limitEnergy / 2 at h
  linarith

theorem firstHeadResidual_pairing_sq_le :
    (inner ℝ firstHeadResidual hilbertOne) ^ 2 ≤
      ‖firstHeadResidual‖ ^ 2 * limitEnergy := by
  have hc := norm_inner_le_norm (𝕜 := ℝ) limitResidual firstHeadResidual
  rw [Real.norm_eq_abs, firstHeadResidual_pairing_limitResidual] at hc
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hc
  rw [sq_abs, mul_pow] at hs
  change (inner ℝ firstHeadResidual hilbertOne) ^ 2 ≤
    limitEnergy * ‖firstHeadResidual‖ ^ 2 at hs
  nlinarith

/-- The positive mean of the first-head defect is comparable to its own energy,
with explicit constants independent of all conductor cutoffs. -/
theorem firstHeadResidual_pairing_energy_bounds :
    (2 - Real.sqrt 2) * ‖firstHeadResidual‖ ^ 2 ≤
      inner ℝ firstHeadResidual hilbertOne ∧
    inner ℝ firstHeadResidual hilbertOne ≤
      (2 + Real.sqrt 2) * ‖firstHeadResidual‖ ^ 2 := by
  let t : ℝ := ‖firstHeadResidual‖ ^ 2
  let h : ℝ := inner ℝ firstHeadResidual hilbertOne
  have ht : 0 ≤ t := sq_nonneg _
  have hd : limitEnergy ≤ 4 * h - 2 * t := firstHeadResidual_energy_pairing_bound
  have hc : h ^ 2 ≤ t * limitEnergy := firstHeadResidual_pairing_sq_le
  have hm := mul_le_mul_of_nonneg_left hd ht
  have hb : (h - 2 * t) ^ 2 ≤ 2 * t ^ 2 := by nlinarith
  have hs : (Real.sqrt 2 * t) ^ 2 = 2 * t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hn : 0 ≤ Real.sqrt 2 * t := mul_nonneg (Real.sqrt_nonneg _) ht
  have ha : |h - 2 * t| ≤ Real.sqrt 2 * t :=
    (sq_le_sq₀ (abs_nonneg _) hn).mp (by rw [sq_abs, hs]; exact hb)
  rcases abs_le.mp ha with ⟨hl, hu⟩
  change (2 - Real.sqrt 2) * t ≤ h ∧ h ≤ (2 + Real.sqrt 2) * t
  constructor <;> nlinarith

/-- The first-head and constant projection defects vanish together and are
uniformly comparable even before either one is proved to vanish. -/
theorem firstHeadResidual_limitEnergy_bounds :
    (6 - 4 * Real.sqrt 2) * ‖firstHeadResidual‖ ^ 2 ≤ limitEnergy ∧
    limitEnergy ≤ (6 + 4 * Real.sqrt 2) * ‖firstHeadResidual‖ ^ 2 := by
  let t : ℝ := ‖firstHeadResidual‖ ^ 2
  let h : ℝ := inner ℝ firstHeadResidual hilbertOne
  have ht : 0 ≤ t := sq_nonneg _
  have hδ : 0 ≤ limitEnergy := sq_nonneg _
  have hd : limitEnergy ≤ 4 * h - 2 * t := firstHeadResidual_energy_pairing_bound
  have hc : h ^ 2 ≤ t * limitEnergy := firstHeadResidual_pairing_sq_le
  have hleft : 0 ≤ limitEnergy + 2 * t := by positivity
  have hright : 0 ≤ 4 * h := by linarith
  have hle : limitEnergy + 2 * t ≤ 4 * h := by linarith
  have hsquare := (sq_le_sq₀ hleft hright).mpr hle
  have hb : (limitEnergy - 6 * t) ^ 2 ≤ 32 * t ^ 2 := by nlinarith
  have hs : (4 * Real.sqrt 2 * t) ^ 2 = 32 * t ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hn : 0 ≤ 4 * Real.sqrt 2 * t := by positivity
  have ha : |limitEnergy - 6 * t| ≤ 4 * Real.sqrt 2 * t :=
    (sq_le_sq₀ (abs_nonneg _) hn).mp (by rw [sq_abs, hs]; exact hb)
  rcases abs_le.mp ha with ⟨hl, hu⟩
  change (6 - 4 * Real.sqrt 2) * t ≤ limitEnergy ∧
    limitEnergy ≤ (6 + 4 * Real.sqrt 2) * t
  constructor <;> nlinarith

theorem firstHeadResidual_norm_sq_eq_limitError :
    ‖firstHeadResidual‖ ^ 2 = singleHeadLimitError := rfl

namespace SignedCovariance

/-- The limiting normal energy measures the original constant defect within
absolute constants. Nondensity is an explicit hypothesis, not a conclusion. -/
theorem singleHeadNormal_global_defect_comparison (Z : ThresholdHilbert)
    (hlim : Tendsto (fun M => windowNormal 1 M (by omega)) atTop (𝓝 Z))
    (hd : closedSpace ≠ ⊤) :
    6 - 4 * Real.sqrt 2 ≤ limitEnergy * (‖Z‖ ^ 2 + 2) ∧
    limitEnergy * (‖Z‖ ^ 2 + 2) ≤ 6 + 4 * Real.sqrt 2 := by
  have ht : 0 < singleHeadLimitError := by
    have hn : 0 ≤ singleHeadLimitError := sq_nonneg _
    have hne : singleHeadLimitError ≠ 0 :=
      fun h => hd (singleHeadLimitError_eq_zero_iff_density.mp h)
    exact lt_of_le_of_ne hn (Ne.symm hne)
  have he := singleHeadNormal_limit_energy Z hlim hd
  have hb := firstHeadResidual_limitEnergy_bounds
  rw [firstHeadResidual_norm_sq_eq_limitError] at hb
  have hm : singleHeadLimitError * (‖Z‖ ^ 2 + 2) = 1 := by
    rw [he]
    ring_nf
    exact mul_inv_cancel₀ (ne_of_gt ht)
  have hc : 0 ≤ ‖Z‖ ^ 2 + 2 := by positivity
  constructor
  · have hh := mul_le_mul_of_nonneg_right hb.1 hc
    nlinarith [hh]
  · have hh := mul_le_mul_of_nonneg_right hb.2 hc
    nlinarith [hh]

end SignedCovariance
end RiemannResearch.RH.Pareto.CoefficientStabilization
