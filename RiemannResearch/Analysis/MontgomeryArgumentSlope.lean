/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryArgumentWindowVariance
import RiemannResearch.Analysis.ZeroDPPWindowLattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Microscopic argument variance at shrinking widths

The signed upper-height cutoff and gamma corrections are both proportional
to the unfolded width on bounded width ranges. Dividing by the width thus
preserves the comparison even along arbitrarily rapidly shrinking widths.
This gives a pair-correlation criterion using the actual count-discrepancy
increment square at a fixed rational width and at a shrinking width. The
finite window identities use the GLSS triangular test, Proposition 2,
https://doi.org/10.1112/mtk.70127.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroDiscrepancy ActualZeroOrdinate ActualZeroCollisionCertificate
open ActualZeroWindowVariance ZeroDPPCorrelation

/-- The triangle-to-argument comparison survives division by any bounded,
eventually positive moving width. No lower bound on its rate is needed. -/
theorem triangle_sub_sq_sub_pureArgument_div_width_tendsto
    (r : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hr : ∀ᶠ T : ℝ in atTop, 0 < r T ∧ r T ≤ B) :
    Tendsto (fun T : ℝ => (unfoldedWindowEnergy T (r T) - (r T) ^ 2 -
      pureArgumentWidthMoment T (r T)) / r T) atTop (𝓝 0) := by
  obtain ⟨A, hA, hclip⟩ := eventually_normalizedWindowClipError_le_width_mul hB
  obtain ⟨K, C, hK, hC, hgamma⟩ := eventually_fullArgumentWidthMoment_sub_pure_le_width hB
  let e := fun T : ℝ => A * (Real.log T / T) + (2 * B) * |unfoldedWindowMean T 1 - 1| +
    (2 * K / T + C * B / (Real.log T) ^ 2)
  have hlog : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hinv : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hmean := ((unfoldedWindowMean_tendsto 1).sub_const 1).abs.const_mul (2 * B)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e, Function.comp_def, div_eq_mul_inv, inv_pow] using
      ((hlog.const_mul A).add hmean).add ((hinv.const_mul (2 * K)).add
        (((hinv.comp Real.tendsto_log_atTop).pow 2).const_mul (C * B)))
  apply squeeze_zero_norm' _ he
  filter_upwards [hclip, hgamma, eventually_window_sub_argument_eq hB, hr,
    eventually_gt_atTop (1 : ℝ)] with T hc hg ha hw hT
  let R := r T
  have hR : 0 < R := hw.1
  have hRB : R ≤ B := hw.2
  have hmem : R ∈ Icc 0 B := ⟨hR.le, hRB⟩
  have heq : unfoldedWindowEnergy T R - R ^ 2 - pureArgumentWidthMoment T R =
      normalizedWindowClipError T R R + 2 * R ^ 2 * (unfoldedWindowMean T 1 - 1) +
        (fullArgumentWidthMoment T R - pureArgumentWidthMoment T R) := by
    linarith only [ha R hmem]
  change ‖(unfoldedWindowEnergy T R - R ^ 2 - pureArgumentWidthMoment T R) / R‖ ≤ e T
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hR, heq]
  apply (div_le_iff₀ hR).2
  have hcorr := hc R R hR.le hRB (by simpa [abs_of_pos hR] using hRB)
  have hsq : R ^ 2 ≤ R * B := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hRB hR.le
  have hM : |2 * R ^ 2 * (unfoldedWindowMean T 1 - 1)| ≤
      2 * (R * B) * |unfoldedWindowMean T 1 - 1| := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 * R ^ 2 by positivity)]
    gcongr
  have hG := (hg R hmem).trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC) (sq_nonneg _)))
  exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hcorr hM))
    hG)).trans_eq (by dsimp [e]; ring)

private def equalOrdinateMass (T : ℝ) : ℝ :=
  (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))

private theorem triangle_sub_argument_slope_tendsto (r : ℝ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (hp : ∀ᶠ T in atTop, 0 < r T) :
    Tendsto (fun T : ℝ => unfoldedWindowEnergy T (r T) / r T -
      pureArgumentWidthMoment T (r T) / r T) atTop (𝓝 0) := by
  have hb := hp.and ((hr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono
    fun _ h => h.le)
  have ht := (triangle_sub_sq_sub_pureArgument_div_width_tendsto r zero_le_one hb).add hr
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [hp] with T hT
  field_simp [hT.ne']
  ring

/-- There is an actual shrinking width at which the bare argument variance
per unit width reads the equal-ordinate mass, including all multiplicities. -/
theorem exists_shrinking_pureArgument_reading_collisions :
    ∃ r : ℝ → ℝ, Tendsto r atTop (𝓝 0) ∧ (∀ᶠ T in atTop, 0 < r T) ∧
      Tendsto (fun T : ℝ => pureArgumentWidthMoment T (r T) / r T -
        (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) atTop (𝓝 0) := by
  obtain ⟨r, hr, hp, hc⟩ := exists_shrinking_width_reading_collisions
  refine ⟨r, hr, hp, ?_⟩
  have hmean := hr.mul ((unfoldedWindowMean_tendsto 1).pow 2)
  have he := (hc.add hmean).sub (triangle_sub_argument_slope_tendsto r hr hp)
  simp only [zero_mul, add_zero, sub_zero] at he
  apply he.congr'
  filter_upwards [eventually_supported_width 1, hp, hr.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)), eventually_gt_atTop (1 : ℝ)]
    with T hs hR hR₁ hT
  obtain ⟨hw, hfloor⟩ := hs (r T) hR.le hR₁.le
  have ht := zero_lt_one.trans hT
  have hmeanEq : (Ncount 0 T : ℝ) * (r T / (Real.log T / (2 * Real.pi))) =
      T * unfoldedWindowMean T (r T) := by unfold unfoldedWindowMean; field_simp [ht.ne']
  have hdec := actual_triangle_eq_mean_sq_add_variance T _ _ ht hw hfloor hmeanEq
  change unfoldedWindowEnergy T (r T) = unfoldedWindowMean T (r T) ^ 2 +
    unfoldedWindowVariance T (r T) at hdec
  have hm : unfoldedWindowMean T (r T) = r T * unfoldedWindowMean T 1 := by
    unfold unfoldedWindowMean
    ring
  rw [hdec, hm]
  field_simp [hR.ne']
  ring

/-- Under positive-gap PCC every shrinking positive width reads the same
finite-height collision mass asymptotically. This includes widths above
the smallest positive gap. -/
theorem shrinking_pureArgument_sub_collision_of_PCC (h : PositiveGapPCC) (r : ℝ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (hp : ∀ᶠ T in atTop, 0 < r T) :
    Tendsto (fun T : ℝ => pureArgumentWidthMoment T (r T) / r T -
      (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) atTop (𝓝 0) := by
  have ht : Tendsto (fun T => unfoldedWindowEnergy T (r T) / r T - equalOrdinateMass T)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using (shrinking_positive_gap_limit h hr).const_mul 2)
    filter_upwards [hp, eventually_gt_atTop (1 : ℝ)] with T hR hT
    have hI := intervalIntegral.integral_nonneg (μ := volume) hR.le
      (fun x _ => positiveGapMass_nonneg hT x)
    have hU := intervalIntegral.integral_mono_on (μ := volume) hR.le
      (positiveGapMass_mono hT).intervalIntegrable
      (g := fun _ : ℝ => positiveGapMass T (r T)) intervalIntegrable_const
      (fun x hx => positiveGapMass_mono hT hx.2)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hU
    rw [Real.norm_eq_abs, unfoldedWindowEnergy,
      physicalTriangle_eq_collision_add_positive_gaps hT hR.le]
    change |(r T * equalOrdinateMass T + 2 * _) / r T - equalOrdinateMass T| ≤ _
    rw [add_div, mul_div_cancel_left₀ _ hR.ne', add_sub_cancel_left,
        abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hI) hR.le)]
    apply (div_le_iff₀ hR).2
    linarith only [mul_le_mul_of_nonneg_left hU (show (0 : ℝ) ≤ 2 by norm_num),
      show 2 * (r T * positiveGapMass T (r T)) = 2 * positiveGapMass T (r T) * r T by ring]
  have he := ht.sub (triangle_sub_argument_slope_tendsto r hr hp)
  simp only [sub_zero] at he
  exact he.congr' (Eventually.of_forall fun T => by dsimp [equalOrdinateMass]; ring)

/-- A collision-count-free criterion using only the microscopic variance of
the canonical zeta argument discrepancy. Test its value at each rational
width against the slope at every shrinking positive reference width. -/
theorem positiveGapPCC_iff_shrinkingPureArgumentContrasts :
    PositiveGapPCC ↔ ∀ r : ℝ → ℝ, Tendsto r atTop (𝓝 0) → (∀ᶠ T in atTop, 0 < r T) →
      ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ =>
        pureArgumentWidthMoment T q - (sineWindowEnergy q - (q : ℝ) ^ 2) -
        (q : ℝ) * (pureArgumentWidthMoment T (r T) / r T - 1)) atTop (𝓝 0) := by
  constructor
  · intro h r hr hp q hq
    have h1 := positiveGapPCC_iff_collisionCorrectedPureArgument.mp h q hq
    have h2 := (shrinking_pureArgument_sub_collision_of_PCC h r hr hp).const_mul (q : ℝ)
    have he := h1.sub h2
    simp only [mul_zero, sub_zero] at he
    exact he.congr' (Eventually.of_forall fun T => by dsimp; ring)
  · intro h
    obtain ⟨r, hr, hp, hc⟩ := exists_shrinking_pureArgument_reading_collisions
    apply positiveGapPCC_iff_collisionCorrectedPureArgument.mpr
    intro q hq
    have he := (h r hr hp q hq).add (hc.const_mul (q : ℝ))
    simp only [mul_zero, zero_add] at he
    exact he.congr' (Eventually.of_forall fun T => by dsimp; ring)

/-- Infimum of the argument-square statistic per unit width with its mean
correction, over a fixed interval of positive unfolded widths. -/
def pureArgumentSlopeInfimum (T : ℝ) : ℝ :=
  sInf ((fun r : ℝ => r + pureArgumentWidthMoment T r / r) '' Ioc 0 1)

/-- The width infimum of the pure argument statistic recovers the measured
equal-ordinate mass up to an error tending to zero, regardless of the first
positive gap or the size of the collision mass. -/
theorem pureArgumentSlopeInfimum_sub_collision_tendsto :
    Tendsto (fun T : ℝ => pureArgumentSlopeInfimum T -
      (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) atTop (𝓝 0) := by
  classical
  let v := fun T r : ℝ => r + pureArgumentWidthMoment T r / r
  have hb (T : ℝ) (hT : 1 < T) : BddBelow (v T '' Ioc 0 1) := by
    refine ⟨0, ?_⟩
    rintro x ⟨r, hr, rfl⟩
    have hp : 0 ≤ pureArgumentWidthMoment T r := by
      unfold pureArgumentWidthMoment
      exact div_nonneg (intervalIntegral.integral_nonneg (zero_lt_one.trans hT).le
        (fun _ _ => sq_nonneg _)) (zero_lt_one.trans hT).le
    exact add_nonneg hr.1.le (div_nonneg hp hr.1.le)
  have hn (T : ℝ) : (v T '' Ioc 0 1).Nonempty :=
    ⟨v T 1, 1, ⟨zero_lt_one, le_rfl⟩, rfl⟩
  have hw (T : ℝ) (hT : 1 < T) : ∃ w ∈ Ioc (0 : ℝ) 1,
      v T w < pureArgumentSlopeInfimum T + T⁻¹ := by
    have ht : sInf (v T '' Ioc 0 1) < pureArgumentSlopeInfimum T + T⁻¹ :=
      lt_add_of_pos_right _ (inv_pos.mpr (zero_lt_one.trans hT))
    obtain ⟨x, ⟨w, hm, rfl⟩, hx⟩ := (csInf_lt_iff (hb T hT) (hn T)).mp ht
    exact ⟨w, hm, hx⟩
  let w := fun T : ℝ => if h : 1 < T then (hw T h).choose else 1
  have hw' : ∀ᶠ T : ℝ in atTop, w T ∈ Ioc (0 : ℝ) 1 ∧
      v T (w T) < pureArgumentSlopeInfimum T + T⁻¹ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    simpa [w, hT] using (hw T hT).choose_spec
  let d := fun T : ℝ => (unfoldedWindowEnergy T (w T) - (w T) ^ 2 -
    pureArgumentWidthMoment T (w T)) / w T
  have hd : Tendsto d atTop (𝓝 0) :=
    triangle_sub_sq_sub_pureArgument_div_width_tendsto w zero_le_one (hw'.mono fun _ h => h.1)
  obtain ⟨r, hr, hp, hc⟩ := exists_shrinking_pureArgument_reading_collisions
  have hInv : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hLo := hd.neg.sub hInv
  have hHi := hr.add hc
  simp only [neg_zero, sub_zero] at hLo
  simp only [zero_add] at hHi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo hHi
  · filter_upwards [hw', eventually_gt_atTop (1 : ℝ)] with T hW hT
    have hwpos := hW.1.1
    have hI := intervalIntegral.integral_nonneg (μ := volume) hwpos.le
      (fun u _ => positiveGapMass_nonneg hT u)
    have hlow : equalOrdinateMass T ≤ unfoldedWindowEnergy T (w T) / w T := by
      apply (le_div_iff₀ hwpos).2
      rw [unfoldedWindowEnergy, physicalTriangle_eq_collision_add_positive_gaps hT hwpos.le]
      dsimp [equalOrdinateMass]
      linarith only [hI, mul_comm (w T)
        ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))]
    have heq : unfoldedWindowEnergy T (w T) / w T = v T (w T) + d T := by
      dsimp [v, d]
      field_simp [hwpos.ne'] <;> ring
    change -d T - T⁻¹ ≤ pureArgumentSlopeInfimum T - equalOrdinateMass T
    linarith only [hlow, heq, hW.2]
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hp,
      hr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with T hT hR hR₁
    have hs : pureArgumentSlopeInfimum T ≤ v T (r T) :=
      csInf_le (hb T hT) ⟨r T, ⟨hR, hR₁.le⟩, rfl⟩
    dsimp [v] at hs
    linarith only [hs]

/-- Strict positive-gap PCC is exactly convergence of the microscopic
argument variances at positive rational widths after centering by one
intrinsic infimum over the fixed range (0,1]. -/
theorem positiveGapPCC_iff_pureArgumentSlopeInfimum :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ =>
      pureArgumentWidthMoment T q - (sineWindowEnergy q - (q : ℝ) ^ 2) -
        (q : ℝ) * (pureArgumentSlopeInfimum T - 1)) atTop (𝓝 0) := by
  rw [positiveGapPCC_iff_collisionCorrectedPureArgument]
  constructor
  · intro h q hq
    have he := (h q hq).sub (pureArgumentSlopeInfimum_sub_collision_tendsto.const_mul (q : ℝ))
    simp only [mul_zero, sub_zero] at he
    exact he.congr' (Eventually.of_forall fun T => by dsimp; ring)
  · intro h q hq
    have he := (h q hq).add (pureArgumentSlopeInfimum_sub_collision_tendsto.const_mul (q : ℝ))
    simp only [mul_zero, add_zero] at he
    exact he.congr' (Eventually.of_forall fun T => by dsimp; ring)

end RiemannResearch.Analysis.MontgomeryPositiveGap
