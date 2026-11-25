import RiemannResearch.Analysis.MontgomeryMicroscopicGapPacking

/-! # A positive slope at every escaping submacroscopic gap width

Choosing the integer occupancy level separately at each observation height
bounds the actual positive-gap count at all moving widths. In particular
the lower coefficient remains valid for widths growing more slowly than
log T, where a pointwise Riemann–von Mangoldt remainder is too large.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate

/-- Uniform finite packing after optimization over the integer occupancy.
The two denominator corrections record the final incomplete cell and the
omitted equal-ordinate pairs. -/
theorem microscopic_gap_quadratic_packing_bound {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    let D := unfoldedCutoff T
    let M := ((distinctOrdinates T).card:ℝ)
    (M/D)^2/(2*(1+R/D))-(M/D)/(2*R) ≤ positiveGapMass T R/R := by
  let D := unfoldedCutoff T
  let M := ((distinctOrdinates T).card:ℝ)
  let B := (⌊D/R⌋₊:ℝ)+1
  let k := ⌊M/B⌋₊
  let δ := M/B-(k:ℝ)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hB : 0 < B := by dsimp [B]; positivity
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hd₀ : 0 ≤ δ := sub_nonneg.mpr (Nat.floor_le (div_nonneg hM hB.le))
  have hd₁ : δ ≤ 1 := by
    dsimp only [δ,k]
    linarith only [Nat.lt_floor_add_one (M/B)]
  have hcorr : 0 ≤ B/2*δ*(1-δ) :=
    mul_nonneg (mul_nonneg (by positivity) hd₀) (sub_nonneg.mpr hd₁)
  have he : (k:ℝ)*M-B*((k:ℝ)*(k+1)/2) =
      M^2/(2*B)-M/2 + B/2*δ*(1-δ) := by
    dsimp only [δ]
    field_simp [hB.ne'] <;> ring
  have hp := microscopic_gap_packing_bound hT hR k
  change (k:ℝ)*M-B*((k:ℝ)*(k+1)/2) ≤ D*positiveGapMass T R at hp
  rw [he] at hp
  have hsize : B ≤ D/R+1 := by
    dsimp only [B]
    linarith only [Nat.floor_le (div_nonneg hD.le hR.le)]
  have huv : M^2/(2*(D/R+1)) ≤ M^2/(2*B) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (mul_le_mul_of_nonneg_left hsize (by norm_num))
  have hbnd : M^2/(2*(D/R+1))-M/2 ≤ D*positiveGapMass T R := by
    linarith only [hcorr,hp,huv]
  change (M/D)^2/(2*(1+R/D))-(M/D)/(2*R) ≤ positiveGapMass T R/R
  calc
    _ = (M^2/(2*(D/R+1))-M/2)/(D*R) := by
      rw [show D/R+1=(D+R)/R by field_simp [hR.ne'],
        show 1+R/D=(D+R)/D by field_simp [hD.ne']]
      field_simp [hD.ne',hR.ne',(add_pos hD hR).ne'] <;> ring
    _ ≤ (D*positiveGapMass T R)/(D*R) := div_le_div_of_nonneg_right hbnd (mul_pos hD hR).le
    _ = _ := by field_simp [hD.ne',hR.ne']

/-- Transfer a finite quadratic lower bound expressed in the distinct
height count to every escaping submacroscopic observation schedule. -/
theorem eventually_moving_lower_of_distinct_quadratic (F : ℝ → ℝ → ℝ)
    (hF₀ : ∀ T R : ℝ, 1 < T → 0 < R → 0 ≤ F T R)
    (hF : ∀ T R : ℝ, 1 < T → 0 < R →
      let D := unfoldedCutoff T
      let M := ((distinctOrdinates T).card:ℝ)
      (M/D)^2/(2*(1+R/D))-(M/D)/(2*R) ≤ F T R)
    {κ z : ℝ}
    (hκ : CumulativeDistinctOrdinateProportion κ) (hκ₀ : 0 < κ)
    (r : ℝ → ℝ) (hr : Tendsto r atTop atTop)
    (hscale : Tendsto (fun T : ℝ => r T/unfoldedCutoff T) atTop (𝓝 0))
    (hz : z < κ^2/2) :
    ∀ᶠ T : ℝ in atTop, z < F T (r T) := by
  by_cases hz₀ : z < 0
  · filter_upwards [eventually_gt_atTop (1:ℝ),hr.eventually_gt_atTop 0] with T hT hR
    exact hz₀.trans_le (hF₀ T (r T) hT hR)
  let a := Real.sqrt (2*z)
  have ha₀ : 0 ≤ a := Real.sqrt_nonneg _
  have ha₂ : a^2=2*z := Real.sq_sqrt (mul_nonneg (by norm_num) (le_of_not_gt hz₀))
  have ha : a < κ := (sq_lt_sq₀ ha₀ hκ₀.le).mp (by rw [ha₂]; linarith only [hz])
  let q := (a+κ)/2
  have haq : a < q := by dsimp only [q]; linarith only [ha]
  have hq : q < κ := by dsimp only [q]; linarith only [ha]
  have hq₀ : 0 ≤ q := ha₀.trans haq.le
  have hqz : z < q^2/2 := by
    have hh := (sq_lt_sq₀ ha₀ hq₀).mpr haq
    rw [ha₂] at hh
    linarith only [hh]
  let η := (κ-q)/2
  have hη : 0 < η := half_pos (sub_pos.mpr hq)
  obtain ⟨t,ht⟩ := hκ η hη
  have hfrac := tendsto_count_div_mainTerm.const_mul (κ-η)
  have hqgap : q < (κ-η)*1 := by dsimp only [η]; linarith only [hq]
  have hrinv : Tendsto (fun T : ℝ => (r T)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hr
  have hden := (hscale.const_add 1).const_mul 2
  have hlow := (tendsto_const_nhds (x := q^2)).div hden (by norm_num : (2:ℝ)*(1+0) ≠ 0)
  have hlim := hlow.sub ((tendsto_count_div_mainTerm.mul hrinv).div_const 2)
  have htarget : z < q^2/(2*(1+0))-(1*0)/2 := by simpa using hqz
  filter_upwards [eventually_gt_atTop (1:ℝ),hr.eventually_gt_atTop 0,
    eventually_ge_atTop t,hfrac.eventually (lt_mem_nhds hqgap),
    hlim.eventually (lt_mem_nhds htarget)] with T hT hR hot hqT hval
  let D := unfoldedCutoff T
  let M := ((distinctOrdinates T).card:ℝ)
  let N := (Ncount 0 T:ℝ)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hmain : q < M/D := hqT.trans_le (by
    change (κ-η)*(N/D) ≤ M/D
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (ht T hot) hD.le)
  have hMN : M/D ≤ N/D := div_le_div_of_nonneg_right (by
    dsimp only [M,N]
    exact_mod_cast card_distinctOrdinates_le_count T) hD.le
  change z < q^2/(2*(1+r T/D))-(N/D)*(r T)⁻¹/2 at hval
  rw [show (N/D)*(r T)⁻¹/2 = (N/D)/(2*r T) by field_simp [hR.ne',hD.ne']] at hval
  exact hval.trans_le ((sub_le_sub
    (div_le_div_of_nonneg_right ((sq_le_sq₀ hq₀ (div_nonneg hM hD.le)).mpr hmain.le)
      (by positivity))
    (div_le_div_of_nonneg_right hMN (by positivity))).trans
    (hF T (r T) hT hR))

/-- Every escaping width with R=o(D) has the same unconditional lower slope,
including widths far below log T. Distinct ordinates supply the count and
all multiplicities remain in the observed statistic. -/
theorem eventually_moving_gap_slope_lower_of_distinct_fraction {κ z : ℝ}
    (hκ : CumulativeDistinctOrdinateProportion κ) (hκ₀ : 0 < κ)
    (r : ℝ → ℝ) (hr : Tendsto r atTop atTop)
    (hscale : Tendsto (fun T : ℝ => r T/unfoldedCutoff T) atTop (𝓝 0))
    (hz : z < κ^2/2) :
    ∀ᶠ T : ℝ in atTop, z < positiveGapMass T (r T)/r T :=
  eventually_moving_lower_of_distinct_quadratic (fun T R => positiveGapMass T R/R)
    (fun _ _ hT hR => div_nonneg (positiveGapMass_nonneg hT _) hR.le)
    (fun _ _ hT hR => microscopic_gap_quadratic_packing_bound hT hR) hκ hκ₀ r hr hscale hz

/-- The moving-width lower coefficient from the actual Montgomery–Taylor
proportion. Both the width and the zero cutoff may vary continuously. -/
theorem eventually_moving_gap_slope_lower_montgomeryTaylor (r : ℝ → ℝ) (hr : Tendsto r atTop atTop)
    (hscale : Tendsto (fun T : ℝ => r T/unfoldedCutoff T) atTop (𝓝 0)) {z : ℝ}
    (hz : z < (ThmD.HD 1)^2/2) :
    ∀ᶠ T : ℝ in atTop, z < positiveGapMass T (r T)/r T :=
  eventually_moving_gap_slope_lower_of_distinct_fraction
    montgomeryTaylor_distinctCriticalProportion.distinct_ordinates
    ((by norm_num : (0:ℝ) < 305/457).trans_le montgomeryTaylor_fraction_ge_305_div_457)
    r hr hscale hz

/-- In particular, the measured positive-gap count is eventually greater
than two ninths of every escaping submacroscopic width. -/
theorem eventually_moving_gap_ratio_gt_two_ninths (r : ℝ → ℝ) (hr : Tendsto r atTop atTop)
    (hscale : Tendsto (fun T : ℝ => r T/unfoldedCutoff T) atTop (𝓝 0)) :
    ∀ᶠ T : ℝ in atTop, 2/9 < positiveGapMass T (r T)/r T := by
  apply eventually_moving_gap_slope_lower_montgomeryTaylor r hr hscale
  have hk : (2/3:ℝ) < ThmD.HD 1 := lt_of_lt_of_le (by norm_num) montgomeryTaylor_fraction_ge_305_div_457
  have hs := (sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 2/3) ((by norm_num : (0:ℝ) ≤ 2/3).trans hk.le)).mpr hk
  linarith only [hs]

/-- The double-logarithmic width lies below the pointwise Riemann–von
Mangoldt mesoscopic range and still satisfies the unconditional slope bound. -/
theorem eventually_loglog_gap_ratio_gt_two_ninths :
    ∀ᶠ T : ℝ in atTop,
      2/9 < positiveGapMass T (Real.log (Real.log T))/Real.log (Real.log T) := by
  apply eventually_moving_gap_ratio_gt_two_ninths (fun T => Real.log (Real.log T))
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have h := (Real.log_div_self_tendsto_zero.comp Real.tendsto_log_atTop).mul
    (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0))
  have hl := h.const_mul (2*Real.pi)
  simp only [mul_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  change (2*Real.pi)*((Real.log (Real.log T)/Real.log T)*T⁻¹) =
    Real.log (Real.log T)/(T*Real.log T/(2*Real.pi))
  field_simp [(zero_lt_one.trans hT).ne',(Real.log_pos hT).ne',Real.pi_ne_zero] <;> ring

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.microscopic_gap_quadratic_packing_bound'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms microscopic_gap_quadratic_packing_bound

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_moving_lower_of_distinct_quadratic'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_moving_lower_of_distinct_quadratic

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_moving_gap_slope_lower_of_distinct_fraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_moving_gap_slope_lower_of_distinct_fraction

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_moving_gap_slope_lower_montgomeryTaylor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_moving_gap_slope_lower_montgomeryTaylor

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_moving_gap_ratio_gt_two_ninths'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_moving_gap_ratio_gt_two_ninths

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_loglog_gap_ratio_gt_two_ninths'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_loglog_gap_ratio_gt_two_ninths

end RiemannResearch.Analysis.MontgomeryPositiveGap
