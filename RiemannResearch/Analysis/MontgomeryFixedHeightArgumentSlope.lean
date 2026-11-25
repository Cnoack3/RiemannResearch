/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryArgumentWindowVariance
import RiemannResearch.Analysis.MontgomeryFejerCertificate
import RiemannResearch.Analysis.ZeroDPPWindowLattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The fixed-height right slope of the zeta argument variance

At each fixed height, the right-hand derivative at width zero reads the
complete equal-ordinate collision count. The full count has no upper cutoff
loss below the next distinct ordinate, and the gamma drift contributes a
quadratic error in width on the fixed height interval. The corresponding
integer threshold uses analytic multiplicity and therefore tests for RH
without requiring simplicity of critical-line zeros.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroDiscrepancy ActualZeroOrdinate ActualZeroCollisionCertificate
open ActualZeroWindowVariance OrdinateWindowVariance ZeroDPPCorrelation

private theorem eventually_count_right_zero (T : ℝ) (hT : 0 < T) :
    ∀ᶠ h : ℝ in 𝓝 0, Ncount T (T + h) = 0 := by
  have hd : ∀ᶠ h : ℝ in 𝓝 0, ∀ z ∈ cutoff (T + 1), T < z.im → T + h < z.im := by
    apply (Filter.eventually_all_finset _).2
    intro z _
    by_cases hz : T < z.im
    · filter_upwards [gt_mem_nhds (sub_pos.mpr hz)] with h hh
      exact fun _ => by linarith
    · exact Eventually.of_forall fun _ hh => (hz hh).elim
  filter_upwards [hd, gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with h hgap hh
  have he : zerosIn T (T + h) = ∅ := by
    ext z
    simp only [zerosIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hz, hlow, hhigh⟩
    have hz' : z ∈ cutoff (T + 1) :=
      mem_cutoff.mpr ⟨hz, hT.trans hlow, by linarith⟩
    exact (not_lt_of_ge hhigh) (hgap z hz' hlow)
  simp [Ncount, he]

/-- Below the next ordinate above the cutoff the full centered count square
has exactly the same integral as the clipped centered count square. -/
private theorem centered_integral_eq_full_of_empty_top {T h c : ℝ}
    (hh : 0 ≤ h) (hhT : h ≤ T) (htop : Ncount T (T + h) = 0) :
    (∫ t : ℝ, actualCenteredCount T h c t ^ 2) =
      ∫ t in (0 : ℝ)..T, ((Ncount t (t + h) : ℝ) - c) ^ 2 := by
  apply sub_eq_zero.mp
  rw [actualCenteredMoment_clip_error_eq hh hhT]
  have he : (∫ t in (T - h)..T, (((Ncount t T : ℝ) - c)^2 -
      ((Ncount t (t + h) : ℝ) - c)^2)) = ∫ _t in (T - h)..T, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith : T - h ≤ T)] at ht
    have htH : T ≤ t + h := by linarith [ht.1]
    have hne : Ncount T (t + h) = 0 := by
      have hmono := Ncount_mono (a := T) (c := T) (b := t + h) (d := T + h)
        le_rfl (by linarith [ht.2])
      omega
    have hadd := Ncount_add (a := t) (b := T) (c := t + h) ht.2 htH
    simp only [hne, add_zero] at hadd
    simp [hadd]
  rw [he]
  simp

/-- Before the first positive gap at the fixed cutoff or the admission of the
next ordinate, the centered full count-square is an exact quadratic in width. -/
theorem eventually_fullArgumentWidthMoment_eq_quadratic {T : ℝ} (hT : 1 < T) :
    ∀ᶠ R : ℝ in 𝓝[>] 0, fullArgumentWidthMoment T R =
      R * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) +
        R ^ 2 * (1 - 2 * ((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi)))) := by
  let L := Real.log T / (2 * Real.pi)
  let C := (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))
  let N := (Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))
  have ht := zero_lt_one.trans hT
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hid : Tendsto (fun R : ℝ => R) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall : Tendsto (fun R : ℝ => R / L) (𝓝[>] 0) (𝓝 0) := by
    simpa using hid.div_const L
  obtain ⟨d, hd, hfloor⟩ := exists_ordinate_floor
  obtain ⟨e, he, hv⟩ := exists_variance_polynomial_near_zero T hT
  change ∀ᶠ R : ℝ in 𝓝[>] 0, fullArgumentWidthMoment T R = R * C + R ^ 2 * (1 - 2 * N)
  filter_upwards [self_mem_nhdsWithin, hid.eventually (gt_mem_nhds he),
    hsmall.eventually (gt_mem_nhds hd), hsmall.eventually (gt_mem_nhds ht),
    hsmall.eventually (eventually_count_right_zero T ht)] with R hR hRe hRd hRt htop
  have hRpos : 0 < R := hR
  let m := unfoldedWindowMean T R
  have hW : 0 ≤ R / L := div_nonneg hRpos.le hL.le
  have hi := integral_actualWindowCount T (R / L) hW
    (fun c => hRd.le.trans (hfloor T c))
  have harea : (Ncount 0 T : ℝ) * (R / L) = T * m := by
    dsimp [m, unfoldedWindowMean, L]
    field_simp [ht.ne']
  have hm : m = R * N := by
    dsimp [m, N, unfoldedWindowMean]
    field_simp [ht.ne', (Real.log_pos hT).ne', Real.pi_ne_zero]
  have hc (a : ℝ) : (∫ t : ℝ, actualCenteredCount T (R / L) a t ^ 2) =
      (∫ t : ℝ, actualWindowCount T (R / L) t ^ 2) - (2 * a) * (T * m) + a ^ 2 * T := by
    have hc' := integral_centeredCount_sq (Finset.univ : Finset (Copies T))
      (fun c => c.1.1.im) T (R / L) a
    change (∫ t : ℝ, actualCenteredCount T (R / L) a t ^ 2) =
      (∫ t : ℝ, actualWindowCount T (R / L) t ^ 2) -
        (2 * a) * (∫ t : ℝ, actualWindowCount T (R / L) t) + a ^ 2 * max T 0 at hc'
    simpa only [hi, harea, max_eq_left ht.le] using hc'
  have hcR := centered_integral_eq_full_of_empty_top (c := R) hW hRt.le htop
  have hV := hv R hRpos.le hRe.le
  change (∫ t : ℝ, actualCenteredCount T (R / L) m t ^ 2) / T =
    R * C - (R * N) ^ 2 at hV
  have hF := fullArgumentWidthMoment_eq_count hT hRpos.le
  change fullArgumentWidthMoment T R = (∫ t in (0 : ℝ)..T,
    ((Ncount t (t + R / L) : ℝ) - R) ^ 2) / T at hF
  rw [← hcR, hc R, hm] at hF
  rw [hc m, hm] at hV
  rw [hF]
  field_simp [ht.ne'] at hV ⊢
  nlinarith only [hV]

private theorem fullArgument_fixedHeight_slope {T : ℝ} (hT : 1 < T) :
    Tendsto (fun R : ℝ => fullArgumentWidthMoment T R / R) (𝓝[>] 0)
      (𝓝 ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))) := by
  let C := (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))
  let N := (Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))
  have hid : Tendsto (fun R : ℝ => R) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun R : ℝ => C + R * (1 - 2 * N)) (𝓝[>] 0) (𝓝 C) := by
    simpa using (tendsto_const_nhds (x := C)).add (hid.mul_const (1 - 2 * N))
  apply hlim.congr'
  filter_upwards [eventually_fullArgumentWidthMoment_eq_quadratic hT, self_mem_nhdsWithin]
    with R hR hr
  change fullArgumentWidthMoment T R = R * C + R ^ 2 * (1 - 2 * N) at hR
  change C + R * (1 - 2 * N) = fullArgumentWidthMoment T R / R
  rw [hR]
  field_simp [(show 0 < R from hr).ne']

/-- At fixed height the complete gamma correction is bounded quadratically
in the shrinking width. -/
theorem full_sub_pure_fixedHeight_width_bound {T : ℝ} (hT : 1 < T) :
    ∃ B : ℝ, ∀ᶠ R : ℝ in 𝓝[>] 0,
      |fullArgumentWidthMoment T R - pureArgumentWidthMoment T R| ≤ B * R ^ 2 := by
  let L := Real.log T / (2 * Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have ht := zero_lt_one.trans hT
  obtain ⟨M, hMpos, hM⟩ := exists_abs_discrepancy_le_log
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (T + 1))).exists_bound_of_continuousOn
    (RvM.mu_continuous gammaFacts).continuousOn
  obtain ⟨C, hC, hc⟩ := microscopicGammaDrift_mean_sq_le
  let M' := M * (1 + Real.log (T + 5))
  let B := 4 * M' * (K / L + 1) / L
  refine ⟨2 * B / T + C / (Real.log T) ^ 2, ?_⟩
  have hid : Tendsto (fun R : ℝ => R) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hid.eventually (gt_mem_nhds hL)] with R hR hRL
  have hr : 0 < R := hR
  let h := R / L
  have hh : 0 ≤ h := div_nonneg hr.le hL.le
  have hh1 : h ≤ 1 := (div_le_iff₀ hL).2 (by simpa using hRL.le)
  have hbound (a : ℝ) (ha : 0 ≤ a) (haT : a ≤ T) :
      |∫ u in a..a+h, mu u| ≤ K * h := by
    have hle : a ≤ a + h := by linarith
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a+h)
      (f := mu) (C := K) (fun u hu => by
        rw [uIoc_of_le hle] at hu
        exact hK u ⟨ha.trans hu.1.le, by linarith [hu.2]⟩)
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hh] using hb
  have hcross := abs_integral_discrepancy_increment_mul_gammaDrift_le
    (lam := R) (M := M') (B := K * h + R) hh (hh1.trans hT.le)
    (fun t ht' => (hM t ht'.1).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (Real.log_le_log (by linarith [ht'.1] : 0 < t + 4)
        (by linarith [ht'.2] : t + 4 ≤ T + 5))) hMpos.le))
    (by simpa only [zero_add] using
      (show -(K * h + R) ≤ (∫ u in (0 : ℝ)..0+h, mu u) - R by
        linarith only [(abs_le.mp (hbound 0 le_rfl ht.le)).1]))
    (by linarith only [(abs_le.mp (hbound T ht.le le_rfl)).2, hr])
  let x := fun t : ℝ => discrepancy (t + h) - discrepancy t
  let d := microscopicGammaDrift T R
  have hmix : |∫ t in (0 : ℝ)..T, x t * d t| ≤ B * R ^ 2 := by
    have hb : 4 * h * M' * (K * h + R) = B * R ^ 2 := by dsimp [B,h]; ring
    apply LE.le.trans_eq _ hb
    simpa only [x, d, microscopicGammaDrift, smoothCount_sub, h, L] using hcross
  have hnon : 0 ≤ ∫ t in (0 : ℝ)..T, d t ^ 2 :=
    intervalIntegral.integral_nonneg ht.le (fun _ _ => sq_nonneg _)
  rw [fullArgumentWidthMoment_sub_pure]
  change |(2 * (∫ t in (0 : ℝ)..T, x t * d t) + (∫ t in (0 : ℝ)..T, d t ^ 2)) / T| ≤ _
  rw [abs_div, abs_of_pos ht]
  refine (div_le_div_of_nonneg_right (abs_add_le _ _) ht.le).trans ?_
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hnon, add_div]
  have hDrift := hc T R hT hr.le hRL.le
  exact (add_le_add (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmix (by norm_num)) ht.le) hDrift).trans_eq (by ring)

/-- At fixed height the right slope of the bare zeta argument increment
square recovers the full equal-ordinate mass exactly. -/
theorem pureArgument_fixedHeight_slope {T : ℝ} (hT : 1 < T) :
    Tendsto (fun R : ℝ => pureArgumentWidthMoment T R / R) (𝓝[>] 0)
      (𝓝 ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))) := by
  obtain ⟨B, hb⟩ := full_sub_pure_fixedHeight_width_bound hT
  have hid : Tendsto (fun R : ℝ => R) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun R : ℝ =>
      (fullArgumentWidthMoment T R - pureArgumentWidthMoment T R) / R)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using hid.const_mul B)
    filter_upwards [hb, self_mem_nhdsWithin] with R hh hR
    have hr : 0 < R := hR
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr]
    apply (div_le_iff₀ hr).2
    exact hh.trans_eq (by ring)
  have h := (fullArgument_fixedHeight_slope hT).sub hdiff
  simp only [sub_zero] at h
  exact h.congr' (Eventually.of_forall fun R => by dsimp; ring)

/-- Right-hand slope measured from the bare argument-square statistic at
a single height, before passage to a height limit. -/
def pureArgumentRightSlope (T : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun R : ℝ => pureArgumentWidthMoment T R / R)

/-- The local argument slope equals the normalized collision mass at each
height, including analytic multiplicity and distinct zeros at one ordinate. -/
theorem pureArgumentRightSlope_eq_collision {T : ℝ} (hT : 1 < T) :
    pureArgumentRightSlope T = (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) :=
  (pureArgument_fixedHeight_slope hT).limUnder_eq

/-- Positive-gap PCC is equivalent to the rational-width argument variance
limits after subtracting the measured right slope at each finite height.
All data on the right are argument variances. -/
theorem positiveGapPCC_iff_fixedHeightArgumentSlopes :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ =>
      pureArgumentWidthMoment T q - (sineWindowEnergy q - (q : ℝ) ^ 2) -
        (q : ℝ) * (pureArgumentRightSlope T - 1)) atTop (𝓝 0) := by
  rw [positiveGapPCC_iff_collisionCorrectedPureArgument]
  have he (q : ℚ) : (fun T : ℝ => pureArgumentWidthMoment T q -
      (sineWindowEnergy q - (q : ℝ) ^ 2) - (q : ℝ) * (pureArgumentRightSlope T - 1))
      =ᶠ[atTop] (fun T : ℝ => pureArgumentWidthMoment T q - (sineWindowEnergy q - (q : ℝ) ^ 2) -
        (q : ℝ) * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) - 1)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    rw [pureArgumentRightSlope_eq_collision hT]
  constructor <;> intro h q hq
  · exact (h q hq).congr' (he q).symm
  · exact (h q hq).congr' (he q)

/-- The multiplicity-adjusted one-unit margin around the fixed-height
argument slope detects exactly whether every zero below the cutoff is on
the critical line. -/
theorem pureArgument_fixedHeight_critical_line_iff {T : ℝ} (hT : 1 < T) :
    (∀ᶠ R : ℝ in 𝓝[>] 0, (T * Real.log T / (2 * Real.pi)) *
      (pureArgumentWidthMoment T R / R) < (analyticPairCount T : ℝ) + 1) ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  let D := T * Real.log T / (2 * Real.pi)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hlim := (pureArgument_fixedHeight_slope hT).const_mul D
  change Tendsto (fun R : ℝ => D * (pureArgumentWidthMoment T R / R)) (𝓝[>] 0)
    (𝓝 (D * ((actualCollision T : ℝ) / D))) at hlim
  rw [mul_div_cancel₀ _ hD.ne'] at hlim
  constructor
  · intro h ρ hρ
    have he : (actualCollision T : ℝ) ≤ (analyticPairCount T : ℝ) + 1 :=
      le_of_tendsto hlim (h.mono fun _ hR => hR.le)
    have hn : actualCollision T ≤ analyticPairCount T + 1 := by exact_mod_cast he
    have hid := collision_eq_analytic_add_distinctZeroCollision T
    by_contra hoff
    have htwo := two_le_distinctZeroCollision_of_off_line hρ hoff
    omega
  · intro hall
    rw [(collision_eq_analyticPairCount_iff T).mpr hall] at hlim
    exact hlim.eventually (gt_mem_nhds (by linarith))

/-- RH is equivalent to the cofinal family of actual fixed-height right-slope
tests. This formulation allows arbitrary multiplicity on the critical line. -/
theorem cofinal_pureArgument_fixedHeight_iff_RH :
    (∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧ 1 < T ∧ ∀ᶠ R : ℝ in 𝓝[>] 0,
      (T * Real.log T / (2 * Real.pi)) * (pureArgumentWidthMoment T R / R) <
        (analyticPairCount T : ℝ) + 1) ↔ RiemannHypothesis := by
  rw [← MontgomeryFormFactor.cofinal_fejer_critical_line_iff_RH]
  constructor
  · intro h H
    obtain ⟨T, hHT, hT, hs⟩ := h H
    obtain ⟨R, hR, htest⟩ := (MontgomeryFormFactor.fejer_critical_line_iff hT).mpr
      ((pureArgument_fixedHeight_critical_line_iff hT).mp hs)
    exact ⟨T, R, hHT, hT, hR, htest⟩
  · intro h H
    obtain ⟨T, R, hHT, hT, hR, htest⟩ := h H
    exact ⟨T, hHT, hT, (pureArgument_fixedHeight_critical_line_iff hT).mpr
      ((MontgomeryFormFactor.fejer_critical_line_iff hT).mp ⟨R, hR, htest⟩)⟩

end RiemannResearch.Analysis.MontgomeryPositiveGap
