import RiemannResearch.Analysis.MontgomeryArgumentWindowVariance
import RiemannResearch.Analysis.MontgomeryFejerCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # One prescribed argument-variance width on the integer collision scale

For centers at most one half, clipping an integer window count reduces its
squared deviation. Centering the exact gamma increment at the unfolded width
also makes its signed cross term quadratic in that width. These estimates
give a one-sided comparison to the integer collision count at R = T⁻².
The resulting cofinal RH criterion preserves analytic multiplicities.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroDiscrepancy ActualZeroOrdinate ActualZeroCollisionCertificate
open ActualZeroWindowVariance

/-- At centers equal to the width, the exact gamma correction is quadratic
in the width uniformly over the full interval [0,1]. -/
theorem eventually_full_sub_pureArgument_quadratic :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, ∀ R ∈ Icc (0 : ℝ) 1,
      |fullArgumentWidthMoment T R - pureArgumentWidthMoment T R| ≤
        (B / T + B / (Real.log T) ^ 2) * R ^ 2 := by
  obtain ⟨K,hK,hcross⟩ := eventually_centered_discrepancy_gamma_cross_le_width_sq
  obtain ⟨C,hC,hdrift⟩ := microscopicGammaDrift_mean_sq_le
  let B := max (2*K) C
  have hB : 0 ≤ B := hC.trans (le_max_right _ _)
  refine ⟨B,hB,?_⟩
  filter_upwards [hcross,eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.pi)] with T hc hT hl R hR
  have ht := zero_lt_one.trans hT
  let h := R / (Real.log T / (2 * Real.pi))
  let x := fun t : ℝ => discrepancy (t+h) - discrepancy t
  let d := microscopicGammaDrift T R
  have hmix : |∫ t in (0 : ℝ)..T, x t * d t| ≤ K * R ^ 2 := by
    simpa only [x,d,microscopicGammaDrift,h,smoothCount_sub] using hc R hR
  have hnon : 0 ≤ ∫ t in (0 : ℝ)..T, d t ^ 2 :=
    intervalIntegral.integral_nonneg ht.le (fun _ _ => sq_nonneg _)
  have hD := hdrift T R hT hR.1 (hR.2.trans ((le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    (by simpa using hl)))
  rw [fullArgumentWidthMoment_sub_pure]
  change |(2 * (∫ t in (0 : ℝ)..T, x t * d t) + (∫ t in (0 : ℝ)..T, d t ^ 2)) / T| ≤ _
  rw [abs_div, abs_of_pos ht]
  refine (div_le_div_of_nonneg_right (abs_add_le _ _) ht.le).trans ?_
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hnon, add_div]
  have hm : 2 * |∫ t in (0 : ℝ)..T, x t * d t| ≤ B * R^2 := by
    calc _ ≤ 2 * (K * R^2) := mul_le_mul_of_nonneg_left hmix (by norm_num)
         _ = 2*K*R^2 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have hr := hD.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right (2*K) C) (sq_nonneg _)) (sq_nonneg _))
  exact (add_le_add (div_le_div_of_nonneg_right hm ht.le) hr).trans_eq (by ring)


/-- The actual positive-gap primitive, signed upper cutoff, mean correction,
and full gamma correction together give the complete bare-argument statistic
uniformly over any bounded nonnegative width interval. -/
theorem eventually_pureArgument_sub_collision_eq {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in atTop, ∀ R ∈ Icc (0 : ℝ) B,
      pureArgumentWidthMoment T R -
        R * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) =
        2 * (∫ u in (0 : ℝ)..R, positiveGapMass T u) -
          R ^ 2 * (2 * unfoldedWindowMean T 1 - 1) -
          normalizedWindowClipError T R R -
          (fullArgumentWidthMoment T R - pureArgumentWidthMoment T R) := by
  filter_upwards [eventually_window_sub_argument_eq hB,eventually_gt_atTop (1 : ℝ)]
    with T hwin hT R hR
  have hE := physicalTriangle_eq_collision_add_positive_gaps hT hR.1
  change unfoldedWindowEnergy T R = _ at hE
  linarith only [hE,hwin R hR,show R ^ 2 * (2 * unfoldedWindowMean T 1 - 1) =
    R ^ 2 + 2 * R ^ 2 * (unfoldedWindowMean T 1 - 1) by ring]


/-- At every sufficiently high cutoff and every width at most one half there is
the same one-sided bound on the collision mass. There is no minimum-gap
condition on the chosen width. -/
theorem eventually_collision_le_pureArgument_div_add_width :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ R ∈ Ioc (0 : ℝ) (1 / 2),
      (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) ≤
        pureArgumentWidthMoment T R / R + K * R := by
  obtain ⟨B,hB,hfull⟩ := eventually_full_sub_pureArgument_quadratic
  refine ⟨3+2*B,by positivity,?_⟩
  filter_upwards [hfull,eventually_window_sub_argument_eq (show (0:ℝ) ≤ 1 by norm_num),
    eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2 * Real.pi)),
    (unfoldedWindowMean_tendsto 1).eventually (gt_mem_nhds (show (1:ℝ) < 2 by norm_num))]
    with T hf hwin hT hlog hmean R hr
  have h₁ : R ≤ 1 := hr.2.trans (by norm_num)
  have hmem : R ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le,h₁⟩
  have hp : 0 < 2 * Real.pi := by positivity
  have hl : 1 ≤ Real.log T := (le_max_left _ _).trans hlog
  have hL : 1 ≤ Real.log T / (2 * Real.pi) := (le_div_iff₀ hp).2
    (by simpa using (le_max_right (1:ℝ) (2*Real.pi)).trans hlog)
  have hw : R / (Real.log T / (2 * Real.pi)) ≤ T :=
    (div_le_self hr.1.le hL).trans (h₁.trans hT.le)
  have hclip := normalizedWindowClipError_nonpos_of_center_le_half hT hr.1.le hw hr.2
  have hg := (abs_le.mp (hf R hmem)).2
  have hrate : B / T + B / (Real.log T)^2 ≤ 2*B := by
    have hlog2 : 1 ≤ (Real.log T)^2 := by nlinarith only [hl, sq_nonneg (Real.log T-1)]
    linarith only [div_le_self hB hT.le,div_le_self hB hlog2]
  have hg' := hg.trans (mul_le_mul_of_nonneg_right hrate (sq_nonneg _))
  have hmean' := mul_le_mul_of_nonneg_left (show unfoldedWindowMean T 1 - 1 ≤ 1 by linarith)
    (show 0 ≤ 2 * R^2 by positivity)
  have hwin' := hwin R hmem
  let C := (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))
  have hcol : R * C ≤ unfoldedWindowEnergy T R := by
    rw [unfoldedWindowEnergy,physicalTriangle_eq_collision_add_positive_gaps hT hr.1.le]
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
      (intervalIntegral.integral_nonneg hr.1.le (fun u _ => positiveGapMass_nonneg hT u)))
  change C ≤ pureArgumentWidthMoment T R / R + (3+2*B) * R
  rw [show pureArgumentWidthMoment T R / R + (3+2*B) * R =
    (pureArgumentWidthMoment T R + (3+2*B) * R^2) / R by field_simp [hr.1.ne']]
  apply (le_div_iff₀ hr.1).2
  linarith only [hcol,hwin',hclip,hg',hmean',mul_comm C R,
    show (3+2*B)*R^2 = 3*R^2 + 2*B*R^2 by ring]

/-- Once the width times the zero-count main term tends to zero, the bare
variance gives an upper bound with vanishing error on the integer pair-count
scale. Extra distinct pairs inside the window have the favorable sign. -/
theorem eventually_collision_lt_prescribed_argument_add (r : ℝ → ℝ)
    (hr : ∀ᶠ T : ℝ in atTop, r T ∈ Ioc (0 : ℝ) (1 / 2))
    (hscale : Tendsto (fun T : ℝ => (T * Real.log T / (2 * Real.pi)) * r T) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, (actualCollision T : ℝ) <
      (T * Real.log T / (2 * Real.pi)) * (pureArgumentWidthMoment T (r T) / r T) + ε := by
  obtain ⟨K,hK,hbound⟩ := eventually_collision_le_pureArgument_div_add_width
  have hk : Tendsto (fun T : ℝ => ((T * Real.log T / (2 * Real.pi)) * r T) * K)
      atTop (𝓝 0) := by simpa using hscale.mul_const K
  filter_upwards [hbound,hr,eventually_gt_atTop (1 : ℝ),hk.eventually (gt_mem_nhds hε)]
    with T hT hrT ht hsmall
  let D := T * Real.log T / (2 * Real.pi)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans ht) (Real.log_pos ht)) (by positivity)
  have hc := (div_le_iff₀ hD).1 (hT (r T) hrT)
  change (actualCollision T : ℝ) < D * (pureArgumentWidthMoment T (r T) / r T) + ε
  change D * r T * K < ε at hsmall
  exact hc.trans_lt (by
    rw [show (pureArgumentWidthMoment T (r T) / r T + K * r T) * D =
      D * (pureArgumentWidthMoment T (r T) / r T) + D * r T * K by ring]
    exact add_lt_add_of_le_of_lt le_rfl hsmall)


/-- A shrinking bare variance controls the complete multiplicity-weighted
off-line count up to arbitrarily small absolute error whenever the chosen
width is little-o of the inverse zero-count normalizer. -/
theorem eventually_offCount_lt_prescribed_argument_excess (r : ℝ → ℝ)
    (hr : ∀ᶠ T : ℝ in atTop, r T ∈ Ioc (0 : ℝ) (1 / 2))
    (hscale : Tendsto (fun T : ℝ => (T * Real.log T / (2 * Real.pi)) * r T) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, (offCount T : ℝ) <
      (T * Real.log T / (2 * Real.pi)) * (pureArgumentWidthMoment T (r T) / r T) -
        (analyticPairCount T : ℝ) + ε := by
  filter_upwards [eventually_collision_lt_prescribed_argument_add r hr hscale hε] with T hc
  have hcount : (offCount T : ℝ) + (analyticPairCount T : ℝ) ≤ (actualCollision T : ℝ) := by
    exact_mod_cast off_count_add_analytic_le_collision T
  linarith only [hc,hcount]

/-- For every prescribed width with vanishing absolute error, a cofinal
variance excess bounded by a fixed number below two forces RH.
An off-line zero and its reflected partner contribute at least two actual
pairs beyond the analytic multiplicity diagonal at every larger cutoff. -/
theorem riemannHypothesis_of_prescribed_argument_margin (r : ℝ → ℝ)
    (hr : ∀ᶠ T : ℝ in atTop, r T ∈ Ioc (0 : ℝ) (1 / 2))
    (hscale : Tendsto (fun T : ℝ => (T * Real.log T / (2 * Real.pi)) * r T) atTop (𝓝 0))
    {c : ℝ} (hc : c < 2)
    (h : ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧ 1 < T ∧
      (T * Real.log T / (2 * Real.pi)) * (pureArgumentWidthMoment T (r T) / r T) ≤
        (analyticPairCount T : ℝ) + c) : RiemannHypothesis := by
  obtain ⟨t,ht⟩ := eventually_atTop.mp
    (eventually_collision_lt_prescribed_argument_add r hr hscale (sub_pos.mpr hc))
  apply MontgomeryFormFactor.cofinal_fejer_critical_line_iff_RH.mp
  intro H
  obtain ⟨T,hTH,hT,hA⟩ := h (max H t)
  have hcoll : (actualCollision T : ℝ) < (analyticPairCount T : ℝ) + 2 := by
    linarith only [ht T ((le_max_right _ _).trans hTH),hA]
  have hnat : actualCollision T < analyticPairCount T + 2 := by exact_mod_cast hcoll
  have hall : ∀ z ∈ cutoff T, z.re = 1/2 := by
    intro z hz
    by_contra hoff
    have hbad := two_le_distinctZeroCollision_of_off_line hz hoff
    have heq := collision_eq_analytic_add_distinctZeroCollision T
    omega
  obtain ⟨R,hR,hcheck⟩ := (MontgomeryFormFactor.fejer_critical_line_iff hT).mpr hall
  exact ⟨T,R,(le_max_left _ _).trans hTH,hT,hR,hcheck⟩

/-- A cofinal bare argument-square bound at the single explicit unfolded
width T⁻² suffices for RH. The analytic multiplicity diagonal is retained.
This implication needs only an upper estimate for the specified statistic. -/
theorem riemannHypothesis_of_inverseSquareWidthArgument
    (h : ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧ 1 < T ∧
      (T * Real.log T / (2 * Real.pi)) * (pureArgumentWidthMoment T (T⁻¹ ^ 2) / (T⁻¹ ^ 2)) <
        (analyticPairCount T : ℝ) + 1) : RiemannHypothesis := by
  let r := fun T : ℝ => T⁻¹ ^ 2
  have hinv : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hr₀ : Tendsto r atTop (𝓝 0) := by simpa [r] using hinv.pow 2
  have hr : ∀ᶠ T : ℝ in atTop, r T ∈ Ioc (0 : ℝ) (1 / 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hr₀.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))] with T ht hsmall
    exact ⟨pow_pos (inv_pos.mpr ht) 2,hsmall.le⟩
  have hlog : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hs : Tendsto (fun T : ℝ => T * Real.log T / (2 * Real.pi) * r T) atTop (𝓝 0) := by
    have hi := hlog.div_const (2 * Real.pi)
    simp only [zero_div] at hi
    apply hi.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T ht
    dsimp [r]
    field_simp [ht.ne',Real.pi_ne_zero]
  apply riemannHypothesis_of_prescribed_argument_margin r hr hs (c := 1) (by norm_num)
  intro H
  obtain ⟨T,hTH,hT,hA⟩ := h H
  exact ⟨T,hTH,hT,hA.le⟩

end RiemannResearch.Analysis.MontgomeryPositiveGap
