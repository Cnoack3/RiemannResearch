import RiemannResearch.Analysis.MontgomeryMacroscopicGapSecondTerm
import RiemannResearch.Analysis.MontgomeryGapRowDuality

/-! # The integrated logarithmic density model for actual positive gaps

The Riemann–von Mangoldt approximation to the cumulative count supplies a
single uniform error of order 1/T for the macroscopic pair model. The model
density has an integrable logarithmic singularity at zero.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate

/-- The logarithmic correction to the one-point model density. -/
def logHeightDensity (u : ℝ) : ℝ := Real.log u - Real.log (2*Real.pi)

private theorem logHeightDensity_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable logHeightDensity volume a b :=
  intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_const

/-- Logarithmic model density with height logarithm L. -/
def modelHeightDensity (L u : ℝ) : ℝ := 1 + logHeightDensity u/L

/-- Primitive of the logarithmic model density. -/
def modelHeightCount (L x : ℝ) : ℝ := x+heightCountSecondProfile x/L

/-- The one-point model density is locally interval integrable at every height logarithm. -/
theorem modelHeightDensity_intervalIntegrable (L a b : ℝ) :
    IntervalIntegrable (modelHeightDensity L) volume a b :=
  intervalIntegrable_const.add ((logHeightDensity_intervalIntegrable a b).div_const L)

/-- Every oriented integral of the single-height model equals the primitive increment. -/
theorem modelHeightCount_sub (L x y : ℝ) :
    modelHeightCount L y - modelHeightCount L x = ∫ u in x..y, modelHeightDensity L u := by
  unfold modelHeightDensity
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => (1:ℝ))
    (g := fun u => logHeightDensity u/L) intervalIntegrable_const
    ((logHeightDensity_intervalIntegrable x y).div_const L),
    intervalIntegral.integral_const,intervalIntegral.integral_div]
  unfold logHeightDensity
  rw [intervalIntegral.integral_sub (f := Real.log) (g := fun _ => Real.log (2*Real.pi))
    intervalIntegral.intervalIntegrable_log' intervalIntegrable_const,integral_log,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul,modelHeightCount,heightCountSecondProfile]
  ring

/-- The smooth pair model is exactly quadratic in the reciprocal logarithm. -/
def macroscopicGapDensityModel (L c : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, modelHeightDensity L u *
    (modelHeightCount L u - modelHeightCount L (max 0 (u-c)))

/-- A uniform O(1/T) approximation to all clipped macroscopic fractions
follows from the same-order one-point cumulative estimate. -/
theorem eventually_macroscopic_gap_density_model_of_uniform_count
    (hcount : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc (0:ℝ) 1,
      |scaledHeightCount T u - (u + heightCountSecondProfile u / Real.log T)| ≤ K/T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, 0 ≤ c →
      |positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
        macroscopicGapDensityModel (Real.log T) c| ≤ C/T := by
  obtain ⟨K,hK,hE⟩ := hcount
  let A := ∫ u in (0:ℝ)..1, |logHeightDensity u|
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => abs_nonneg _)
  refine ⟨2*K*(3+A),by positivity,?_⟩
  filter_upwards [hE,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_count_div_mainTerm.eventually_lt_const (show (1:ℝ) < 2 by norm_num)] with T hFT hT hL hN
  intro c hc
  let L := Real.log T
  have hL₀ := Real.log_pos hT
  have hw := modelHeightDensity_intervalIntegrable L 0 1
  have hGc : Continuous (modelHeightCount L) := continuous_id.add (continuous_heightCountSecondProfile.div_const L)
  have hu : (∫ u in (0:ℝ)..1, |modelHeightDensity L u|) ≤ 1+A := by
    have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one (f := fun u => |modelHeightDensity L u|)
      hw.abs (g := fun u => 1+|logHeightDensity u|)
      (intervalIntegrable_const.add (logHeightDensity_intervalIntegrable 0 1).abs) (fun u _ => by
        apply (abs_add_le _ _).trans
        rw [abs_one,abs_div,abs_of_pos hL₀]
        exact add_le_add le_rfl (div_le_self (abs_nonneg _) hL))
    rw [intervalIntegral.integral_add intervalIntegrable_const (logHeightDensity_intervalIntegrable 0 1).abs,
      intervalIntegral.integral_const] at h
    simpa only [sub_zero,smul_eq_mul,one_mul,A] using h
  have h := positiveGapMass_density_model_error_le hT hc hw hGc
    (fun x _ y _ => modelHeightCount_sub L x y) hFT
  apply h.trans
  have ht := zero_lt_one.trans hT
  change (Ncount 0 T : ℝ)/unfoldedCutoff T < 2 at hN
  calc
    2*(K/T)*((Ncount 0 T : ℝ)/unfoldedCutoff T+(∫ u in (0:ℝ)..1, |modelHeightDensity L u|))
      ≤ 2*(K/T)*(3+A) := mul_le_mul_of_nonneg_left (by linarith only [hN,hu])
        (by positivity)
    _ = _ := by ring

/-- The actual positive-gap mass has a single O(1/T) model error bound for
every nonnegative fraction of the full unfolded height. -/
theorem eventually_macroscopic_gap_density_model :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, 0 ≤ c →
      |positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
        macroscopicGapDensityModel (Real.log T) c| ≤ C/T :=
  eventually_macroscopic_gap_density_model_of_uniform_count eventually_scaledHeightCount_second_profile

private def backwardHeightLength (c u : ℝ) : ℝ := u-max 0 (u-c)

private def backwardProfileIncrement (c u : ℝ) : ℝ :=
  heightCountSecondProfile u - heightCountSecondProfile (max 0 (u-c))

private theorem continuous_backwardHeightLength (c : ℝ) : Continuous (backwardHeightLength c) :=
  continuous_id.sub (continuous_const.max (continuous_id.sub continuous_const))

private theorem continuous_backwardProfileIncrement (c : ℝ) : Continuous (backwardProfileIncrement c) :=
  continuous_heightCountSecondProfile.sub (continuous_heightCountSecondProfile.comp
    (continuous_const.max (continuous_id.sub continuous_const)))

private theorem integral_backwardHeightLength {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) :
    (∫ u in (0:ℝ)..1, backwardHeightLength c u) = c-c^2/2 := by
  have hh := continuous_backwardHeightLength c
  rw [← intervalIntegral.integral_add_adjacent_intervals (hh.intervalIntegrable 0 c) (hh.intervalIntegrable c 1)]
  have h1 : (∫ u in (0:ℝ)..c, backwardHeightLength c u) = ∫ u in 0..c, u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hc.1] at hu
    simp [backwardHeightLength,max_eq_left (sub_nonpos.mpr hu.2)]
  have h2 : (∫ u in c..1, backwardHeightLength c u) = ∫ _ in c..1, c := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hc.2] at hu
    rw [backwardHeightLength,max_eq_right (sub_nonneg.mpr hu.1)]
    ring
  rw [h1,h2,integral_id,intervalIntegral.integral_const,smul_eq_mul]
  ring

private def linearModelCoefficient (c : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, backwardProfileIncrement c u + logHeightDensity u * backwardHeightLength c u

/-- The coefficient of the squared reciprocal logarithm. -/
def macroscopicGapThirdCoefficient (c : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, logHeightDensity u * backwardProfileIncrement c u

private theorem macroscopicGapDensityModel_eq_polynomial {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) (L : ℝ) :
    macroscopicGapDensityModel L c = (c-c^2/2)+linearModelCoefficient c/L +
      macroscopicGapThirdCoefficient c/L^2 := by
  let J := fun u => backwardProfileIncrement c u + logHeightDensity u*backwardHeightLength c u
  let V := fun u => logHeightDensity u * backwardProfileIncrement c u
  have hJ : IntervalIntegrable J volume 0 1 :=
    ((continuous_backwardProfileIncrement c).intervalIntegrable _ _).add
      ((logHeightDensity_intervalIntegrable _ _).mul_continuousOn (continuous_backwardHeightLength c).continuousOn)
  have hV : IntervalIntegrable V volume 0 1 :=
    (logHeightDensity_intervalIntegrable _ _).mul_continuousOn (continuous_backwardProfileIncrement c).continuousOn
  have h0 := (continuous_backwardHeightLength c).intervalIntegrable (μ := volume) (0:ℝ) 1
  have he : macroscopicGapDensityModel L c =
      ∫ u in (0:ℝ)..1, (backwardHeightLength c u+J u/L)+V u/L^2 := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only [modelHeightDensity,modelHeightCount,backwardHeightLength,backwardProfileIncrement,
      J,V,div_eq_mul_inv,inv_pow]
    ring
  rw [he,intervalIntegral.integral_add (h0.add (hJ.div_const L)) (hV.div_const (L^2)),
    intervalIntegral.integral_add h0 (hJ.div_const L),intervalIntegral.integral_div,
    intervalIntegral.integral_div,integral_backwardHeightLength hc]
  rfl

private theorem normalized_model_error_tendsto {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hmodel : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, 0 ≤ c →
      |positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
        macroscopicGapDensityModel (Real.log T) c| ≤ C/T) :
    Tendsto (fun T : ℝ => (Real.log T)^n*(positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
      macroscopicGapDensityModel (Real.log T) c)) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := hmodel
  have hl : Tendsto (fun T : ℝ => (Real.log T)^n/T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 n (by norm_num)
  have hu := hl.const_mul C
  simp only [mul_zero] at hu
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hu
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T hm hT
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (Real.log_pos hT).le n)]
  apply (mul_le_mul_of_nonneg_left (hm c hc) (pow_nonneg (Real.log_pos hT).le n)).trans_eq
  ring

/-- The two integral expressions for the first coefficient agree whenever
the measured macroscopic linear coefficient is known. -/
theorem macroscopicGapDensityModel_eq_from_second_term {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1)
    (hmodel : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, 0 ≤ c →
      |positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
        macroscopicGapDensityModel (Real.log T) c| ≤ C/T)
    (hfirst : Tendsto (fun T : ℝ => Real.log T*(positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
      (c-c^2/2))) atTop (𝓝 (macroscopicGapSecondCoefficient c))) :
    ∀ L : ℝ, macroscopicGapDensityModel L c = (c-c^2/2)+macroscopicGapSecondCoefficient c/L +
      macroscopicGapThirdCoefficient c/L^2 := by
  let L := Real.log
  let J := linearModelCoefficient c
  let V := macroscopicGapThirdCoefficient c
  let P := fun T : ℝ => positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T
  let A := c-c^2/2
  have hLinv := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hJV : Tendsto (fun T : ℝ => J+V*(L T)⁻¹) atTop (𝓝 J) := by
    simpa only [Function.comp_def,mul_zero,add_zero] using
      (tendsto_const_nhds (x := J)).add (hLinv.const_mul V)
  have hJ : Tendsto (fun T : ℝ => L T*(P T-A)) atTop (𝓝 J) := by
    have hh := (normalized_model_error_tendsto (n:=1) hc.1 hmodel).add hJV
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    change (L T)^1*(P T-macroscopicGapDensityModel (L T) c)+(J+V*(L T)⁻¹) = _
    rw [macroscopicGapDensityModel_eq_polynomial hc]
    dsimp only [A,J,V,L]
    field_simp [(Real.log_pos hT).ne'] <;> ring
  have hcoef := tendsto_nhds_unique hJ hfirst
  intro t
  rw [macroscopicGapDensityModel_eq_polynomial hc]
  change A+J/t+V/t^2 = _
  rw [hcoef]

/-- Identifying the linear coefficient of the density model leaves exactly
the quadratic coefficient in the next-order pair limit. -/
theorem macroscopic_gap_third_term_of_density_model {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1)
    (hmodel : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, 0 ≤ c →
      |positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
        macroscopicGapDensityModel (Real.log T) c| ≤ C/T)
    (hfirst : Tendsto (fun T : ℝ => Real.log T*(positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
      (c-c^2/2))) atTop (𝓝 (macroscopicGapSecondCoefficient c))) :
    Tendsto (fun T : ℝ => (Real.log T)^2*(positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
      (c-c^2/2) - macroscopicGapSecondCoefficient c/Real.log T))
      atTop (𝓝 (macroscopicGapThirdCoefficient c)) := by
  let L := Real.log
  let V := macroscopicGapThirdCoefficient c
  let P := fun T : ℝ => positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T
  let A := c-c^2/2
  have hh := (normalized_model_error_tendsto (n:=2) hc.1 hmodel).add (tendsto_const_nhds (x := V))
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  change (L T)^2*(P T-macroscopicGapDensityModel (L T) c)+V = (L T)^2*(P T-A-macroscopicGapSecondCoefficient c/L T)
  rw [macroscopicGapDensityModel_eq_from_second_term hc hmodel hfirst]
  dsimp only [A,V,L]
  field_simp [(Real.log_pos hT).ne'] <;> ring

private theorem logHeightDensity_sq_intervalIntegrable :
    IntervalIntegrable (fun u => (logHeightDensity u)^2) volume 0 1 := by
  let a := Real.log (2*Real.pi)
  let f := fun u : ℝ => u*(logHeightDensity u)^2-2*heightCountSecondProfile u
  have hc₁ : Continuous (fun u : ℝ =>
      (2*(Real.sqrt u*Real.log (Real.sqrt u))-a*Real.sqrt u)^2) :=
    (((Real.continuous_mul_log.comp Real.continuous_sqrt).const_mul 2).sub
      (Real.continuous_sqrt.const_mul a)).pow 2
  have hc₂ : ContinuousOn (fun u : ℝ => u*(logHeightDensity u)^2) (Icc 0 1) := by
    apply hc₁.continuousOn.congr
    intro u hu
    change u*(logHeightDensity u)^2 = (2*(Real.sqrt u*Real.log (Real.sqrt u))-a*Real.sqrt u)^2
    rw [Real.log_sqrt hu.1]
    dsimp only [logHeightDensity,a]
    symm
    calc
      _ = (Real.sqrt u)^2*(Real.log u-Real.log (2*Real.pi))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hu.1]
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg (g:=f)
  · rw [uIcc_of_le zero_le_one]
    exact hc₂.sub (continuous_heightCountSecondProfile.const_mul 2).continuousOn
  · intro u hu
    have hu₀ : 0 < u := by simpa using hu.1
    have hb := (Real.hasDerivAt_log hu₀.ne').sub_const a
    have hP : HasDerivAt heightCountSecondProfile (logHeightDensity u) u := by
      apply ((hasDerivAt_id u).mul (hb.sub_const 1)).congr_deriv
      dsimp [a,logHeightDensity]
      field_simp [hu₀.ne'] <;> ring
    apply (((hasDerivAt_id u).mul (hb.pow 2)).sub (hP.const_mul 2)).congr_deriv
    dsimp [a,logHeightDensity]
    field_simp [hu₀.ne'] <;> ring
  · exact fun u _ => sq_nonneg _

private theorem integral_logHeightDensity (x y : ℝ) :
    (∫ u in x..y, logHeightDensity u) = heightCountSecondProfile y - heightCountSecondProfile x := by
  unfold logHeightDensity
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_log' intervalIntegrable_const,
    integral_log,intervalIntegral.integral_const,smul_eq_mul]
  unfold heightCountSecondProfile
  ring

private theorem logHeightDensity_nonpos {u : ℝ} (hu : u ∈ Icc 0 1) :
    logHeightDensity u ≤ 0 := by
  have ha : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl : Real.log u ≤ 0 := Real.log_nonpos hu.1 hu.2
  exact sub_nonpos.mpr (hl.trans ha)

private theorem backwardProfileIncrement_abs_le {c u : ℝ} (hc : 0 ≤ c) (hu : u ∈ Icc 0 1) :
    |backwardProfileIncrement c u| ≤ c*(1+|logHeightDensity u|) := by
  let d := max 0 (u-c)
  have hd : 0 ≤ d := le_max_left _ _
  have hdu : d ≤ u := max_le hu.1 (sub_le_self _ hc)
  have hl : u-d ≤ c := by linarith only [le_max_right 0 (u-c)]
  have hI := intervalIntegral.integral_mono_on (μ := volume) hdu
    (f := logHeightDensity) (logHeightDensity_intervalIntegrable d u)
    (g := fun _ => (0:ℝ)) intervalIntegrable_const
    (fun x hx => logHeightDensity_nonpos ⟨hd.trans hx.1,hx.2.trans hu.2⟩)
  simp only [intervalIntegral.integral_zero,integral_logHeightDensity] at hI
  have hlog : 0 ≤ d*(Real.log u-Real.log d) := by
    rcases hd.eq_or_lt with h | h
    · rw [←h,zero_mul]
    · exact mul_nonneg h.le (sub_nonneg.mpr (Real.log_le_log h hdu))
  have he : heightCountSecondProfile u-heightCountSecondProfile d =
      (u-d)*(logHeightDensity u-1)+d*(Real.log u-Real.log d) := by
    dsimp [heightCountSecondProfile,logHeightDensity]
    ring
  change |heightCountSecondProfile u-heightCountSecondProfile d| ≤ _
  rw [abs_of_nonpos hI,abs_of_nonpos (logHeightDensity_nonpos hu)]
  have hb := mul_le_mul_of_nonneg_right hl (show 0 ≤ 1-logHeightDensity u by linarith [logHeightDensity_nonpos hu])
  linarith only [he,hb,hlog]

/-- The quadratic coefficient vanishes at least linearly with the macroscopic
width, uniformly down to zero. -/
theorem exists_abs_macroscopicGapThirdCoefficient_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 ≤ c → |macroscopicGapThirdCoefficient c| ≤ K*c := by
  let W := fun u => |logHeightDensity u|+(logHeightDensity u)^2
  have hW : IntervalIntegrable W volume 0 1 :=
    (logHeightDensity_intervalIntegrable 0 1).abs.add logHeightDensity_sq_intervalIntegrable
  refine ⟨∫ u in (0:ℝ)..1, W u,intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun u => add_nonneg (abs_nonneg _) (sq_nonneg _)),?_⟩
  intro c hc
  unfold macroscopicGapThirdCoefficient
  rw [←intervalIntegral.integral_mul_const]
  apply (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
  apply intervalIntegral.integral_mono_on zero_le_one
    ((logHeightDensity_intervalIntegrable 0 1).mul_continuousOn
      (continuous_backwardProfileIncrement c).continuousOn).abs (hW.mul_const c)
  intro u hu
  rw [abs_mul]
  apply (mul_le_mul_of_nonneg_left (backwardProfileIncrement_abs_le hc hu) (abs_nonneg _)).trans_eq
  dsimp only [W]
  rw [← sq_abs (logHeightDensity u)]
  ring

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_macroscopic_gap_density_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_macroscopic_gap_density_model

end RiemannResearch.Analysis.MontgomeryPositiveGap
