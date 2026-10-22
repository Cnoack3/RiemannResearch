import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Exact normalization and polar cancellation of broad tests

Source: user-provided argument, `signed_gain_agent.md` §10.1, equations (29)–(32).
This source supports the statements and the integration-by-parts and dilation
proof strategy. The RH consumer is the broad-test analysis of the arithmetic
prime-square sector.

All integrals below are real Lebesgue integrals on the whole real line.
The square-root normalizer is defined from the actual integral of a square.
The construction requires only C² regularity and compact support; the intended
smooth bumps supported in (0, 1) are a special case. The dilation results hold
for every R > 0, hence in particular for R ≥ 1.
-/

open MeasureTheory
open scoped Topology

namespace MeasureTheory

/-- Whole-line integration by parts gives the negative derivative-energy cross term. -/
theorem integral_mul_secondDeriv_of_hasCompactSupport
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x * deriv (deriv φ) x) = -(∫ x, (deriv φ x) ^ 2) := by
  have h1 : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have h0c : Continuous φ := hφ.continuous
  have h1c : Continuous (deriv φ) := h1.continuous
  have h2c : Continuous (deriv (deriv φ)) := h1.continuous_deriv_one
  have hi02 : Integrable (φ * deriv (deriv φ)) :=
    (h0c.mul h2c).integrable_of_hasCompactSupport hc.mul_right
  have hi11 : Integrable (deriv φ * deriv φ) :=
    (h1c.mul h1c).integrable_of_hasCompactSupport hc.deriv.mul_right
  have hi01 : Integrable (φ * deriv φ) :=
    (h0c.mul h1c).integrable_of_hasCompactSupport hc.mul_right
  simpa only [pow_two] using
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => (hφ.differentiable (by norm_num) x).hasDerivAt)
      (fun x _ => (h1.differentiable (by norm_num) x).hasDerivAt)
      hi02 hi11 hi01

/-- Exact expansion of the squared differential profile, with the positive cross term. -/
theorem integral_sq_secondDeriv_sub_quarter
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (a : ℝ) :
    (∫ x, (a * deriv (deriv φ) x - φ x / 4) ^ 2) =
      a ^ 2 * (∫ x, (deriv (deriv φ) x) ^ 2) +
      (a / 2) * (∫ x, (deriv φ x) ^ 2) +
      (1 / 16 : ℝ) * (∫ x, (φ x) ^ 2) := by
  have h1 : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have h0c : Continuous φ := hφ.continuous
  have h2c : Continuous (deriv (deriv φ)) := h1.continuous_deriv_one
  have hi00 : Integrable (fun x => φ x ^ 2) := by
    have hi : Integrable (φ * φ) :=
      (h0c.mul h0c).integrable_of_hasCompactSupport hc.mul_right
    simpa only [Pi.mul_def, pow_two] using hi
  have hi22 : Integrable (fun x => deriv (deriv φ) x ^ 2) := by
    have hi : Integrable (deriv (deriv φ) * deriv (deriv φ)) :=
      (h2c.mul h2c).integrable_of_hasCompactSupport hc.deriv.deriv.mul_right
    simpa only [Pi.mul_def, pow_two] using hi
  have hi02 : Integrable (fun x => φ x * deriv (deriv φ) x) :=
    (h0c.mul h2c).integrable_of_hasCompactSupport hc.mul_right
  calc
    _ = ∫ x, (a ^ 2 * deriv (deriv φ) x ^ 2 -
        (a / 2) * (φ x * deriv (deriv φ) x)) +
        (1 / 16 : ℝ) * φ x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (a ^ 2 * (∫ x, deriv (deriv φ) x ^ 2) -
        (a / 2) * (∫ x, φ x * deriv (deriv φ) x)) +
        (1 / 16 : ℝ) * (∫ x, φ x ^ 2) := by
      have hi : Integrable (fun x => a ^ 2 * deriv (deriv φ) x ^ 2 -
          (a / 2) * (φ x * deriv (deriv φ) x)) := by
        simpa only [Pi.sub_def] using
          (hi22.const_mul (a ^ 2)).sub (hi02.const_mul (a / 2))
      rw [integral_add hi (hi00.const_mul (1 / 16)),
        integral_sub (hi22.const_mul (a ^ 2)) (hi02.const_mul (a / 2))]
      simp only [integral_const_mul]
    _ = _ := by
      rw [integral_mul_secondDeriv_of_hasCompactSupport hφ hc]
      ring


/-- One whole-line integration by parts transfers a derivative to an exponential. -/
theorem integral_exp_mul_deriv_of_hasCompactSupport
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (c : ℝ) :
    (∫ x, Real.exp (c * x) * deriv φ x) =
      -c * (∫ x, Real.exp (c * x) * φ x) := by
  have he : Continuous (fun x : ℝ => Real.exp (c * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hd (x : ℝ) :
      HasDerivAt (fun y => Real.exp (c * y)) (Real.exp (c * x) * c) x := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul c).exp
  have hi0 : Integrable ((fun x => Real.exp (c * x)) * φ) :=
    (he.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hi1 : Integrable ((fun x => Real.exp (c * x)) * deriv φ) :=
    (he.mul hφ.continuous_deriv_one).integrable_of_hasCompactSupport hc.deriv.mul_left
  have hi2 : Integrable ((fun x => Real.exp (c * x) * c) * φ) :=
    ((he.mul continuous_const).mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  calc
    _ = -(∫ x, (Real.exp (c * x) * c) * φ x) :=
      integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hd x)
        (fun x _ => (hφ.differentiable (by norm_num) x).hasDerivAt) hi1 hi2 hi0
    _ = -(∫ x, c * (Real.exp (c * x) * φ x)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := by rw [integral_const_mul]; ring

/-- Two integrations by parts transfer the second derivative to an exponential. -/
theorem integral_exp_mul_secondDeriv_of_hasCompactSupport
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (c : ℝ) :
    (∫ x, Real.exp (c * x) * deriv (deriv φ) x) =
      c ^ 2 * (∫ x, Real.exp (c * x) * φ x) := by
  have h1 : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have h0 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  rw [integral_exp_mul_deriv_of_hasCompactSupport h1 hc.deriv,
    integral_exp_mul_deriv_of_hasCompactSupport h0 hc]
  ring

/-- The shifted second derivative kills every exponential with c² = 1/4. -/
theorem integral_exp_mul_secondDeriv_sub_quarter_eq_zero
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {c : ℝ} (hc2 : c ^ 2 = 1 / 4) :
    (∫ x, Real.exp (c * x) * (deriv (deriv φ) x - φ x / 4)) = 0 := by
  have h1 : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have he : Continuous (fun x : ℝ => Real.exp (c * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hi0 : Integrable (fun x => Real.exp (c * x) * φ x) :=
    (he.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hi2 : Integrable (fun x => Real.exp (c * x) * deriv (deriv φ) x) :=
    (he.mul h1.continuous_deriv_one).integrable_of_hasCompactSupport hc.deriv.deriv.mul_left
  simp_rw [mul_sub, ← mul_div_assoc]
  rw [integral_sub hi2 (hi0.div_const 4), integral_div,
    integral_exp_mul_secondDeriv_of_hasCompactSupport hφ hc, hc2]
  ring


/-- A nonzero integral forces strictly positive square integral. -/
theorem integral_sq_pos_of_integral_ne_zero
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hI : (∫ x, φ x) ≠ 0) : 0 < ∫ x, φ x ^ 2 := by
  have hi : Integrable (fun x => φ x ^ 2) := by
    have hi' : Integrable (φ * φ) :=
      (hφ.mul hφ).integrable_of_hasCompactSupport hc.mul_right
    simpa only [Pi.mul_def, pow_two] using hi'
  have hn : 0 ≤ ∫ x, φ x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  refine lt_of_le_of_ne hn ?_
  intro hz
  have hae : (fun x => φ x ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).mp hz.symm
  apply hI
  calc
    (∫ x, φ x) = ∫ x : ℝ, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      exact (sq_eq_zero_iff).mp hx
    _ = 0 := integral_zero _ _

/-- For a nonnegative coefficient, the base bump energy gives a uniform lower bound. -/
theorem integral_sq_secondDeriv_sub_quarter_lower
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {a : ℝ} (ha : 0 ≤ a) :
    (1 / 16 : ℝ) * (∫ x, φ x ^ 2) ≤
      ∫ x, (a * deriv (deriv φ) x - φ x / 4) ^ 2 := by
  rw [integral_sq_secondDeriv_sub_quarter hφ hc]
  have h0 : 0 ≤ ∫ x, deriv (deriv φ) x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have h1 : 0 ≤ ∫ x, deriv φ x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have h2 : 0 ≤ a ^ 2 * (∫ x, deriv (deriv φ) x ^ 2) := mul_nonneg (sq_nonneg _) h0
  have h3 : 0 ≤ (a / 2) * (∫ x, deriv φ x ^ 2) := mul_nonneg (by positivity) h1
  linarith

end MeasureTheory

namespace RiemannResearch.RH

/-- The fixed-support numerator of the broad profile; the broad family uses a = R⁻². -/
noncomputable def broadProfileNumerator (φ : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  a * deriv (deriv φ) x - φ x / 4

/-- Lebesgue L² normalization of the fixed-support broad profile. -/
noncomputable def broadProfileNormalizer (φ : ℝ → ℝ) (a : ℝ) : ℝ :=
  Real.sqrt (∫ x, broadProfileNumerator φ a x ^ 2)

noncomputable def normalizedBroadProfile (φ : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  broadProfileNumerator φ a x / broadProfileNormalizer φ a

/-- Nonzero bump integral ensures that normalization divides by a positive number. -/
theorem broadProfileNormalizer_pos
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hI : (∫ x, φ x) ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    0 < broadProfileNormalizer φ a := by
  apply Real.sqrt_pos.2
  exact lt_of_lt_of_le (mul_pos (by norm_num)
      (integral_sq_pos_of_integral_ne_zero hφ.continuous hc hI))
    (integral_sq_secondDeriv_sub_quarter_lower hφ hc ha)

/-- Exact normalization formula for the fixed-support profile. -/
theorem broadProfileNormalizer_sq
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (a : ℝ) :
    broadProfileNormalizer φ a ^ 2 =
      a ^ 2 * (∫ x, deriv (deriv φ) x ^ 2) +
      (a / 2) * (∫ x, deriv φ x ^ 2) +
      (1 / 16 : ℝ) * (∫ x, φ x ^ 2) := by
  rw [broadProfileNormalizer, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))]
  exact integral_sq_secondDeriv_sub_quarter hφ hc a

/-- The normalized fixed-support profile has unit Lebesgue square integral. -/
theorem normalizedBroadProfile_integral_sq
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hI : (∫ x, φ x) ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x, normalizedBroadProfile φ a x ^ 2) = 1 := by
  simp only [normalizedBroadProfile, div_pow]
  rw [integral_div]
  have hN : broadProfileNormalizer φ a ≠ 0 :=
    ne_of_gt (broadProfileNormalizer_pos hφ hc hI ha)
  have hsq : broadProfileNormalizer φ a ^ 2 =
      ∫ x, broadProfileNumerator φ a x ^ 2 :=
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))
  rw [← hsq, div_self (pow_ne_zero 2 hN)]

end RiemannResearch.RH

namespace MeasureTheory

theorem integral_sq_sqrt_dilate (φ : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x, ((Real.sqrt R)⁻¹ * φ (x / R)) ^ 2) = ∫ x, φ x ^ 2 := by
  simp only [mul_pow, integral_const_mul, div_eq_mul_inv]
  rw [Measure.integral_comp_mul_right (fun y => φ y ^ 2) R⁻¹]
  simp only [inv_inv, abs_of_pos hR, smul_eq_mul, inv_pow, Real.sq_sqrt hR.le]
  exact inv_mul_cancel_left₀ (ne_of_gt hR) _

end MeasureTheory

theorem deriv_const_mul_comp_div (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (k R x : ℝ) :
    deriv (fun y => k * φ (y / R)) x = k * (deriv φ (x / R) / R) := by
  apply HasDerivAt.deriv
  simpa only [div_eq_mul_inv, one_mul, id_eq, Function.comp_def] using
    ((hφ (x / R)).hasDerivAt.comp x ((hasDerivAt_id x).div_const R)).const_mul k

theorem secondDeriv_const_mul_comp_div (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (k R x : ℝ) :
    deriv (deriv (fun y => k * φ (y / R))) x =
      k * (R⁻¹ ^ 2 * deriv (deriv φ) (x / R)) := by
  have hd : deriv (fun y => k * φ (y / R)) =
      fun y => (k / R) * deriv φ (y / R) := by
    funext y
    rw [deriv_const_mul_comp_div φ (hφ.differentiable (by norm_num))]
    ring
  rw [hd, deriv_const_mul_comp_div (deriv φ) hφ.differentiable_deriv_two]
  ring

namespace RiemannResearch.RH

/-- The actual differential operator killing both exponential polar modes. -/
noncomputable def broadPolarOperator (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv v) x - v x / 4

/-- The real, L²-preserving dilation of the compact bump. -/
noncomputable def broadBump (φ : ℝ → ℝ) (R : ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt R)⁻¹ * φ (x / R)

/-- The actual differential image of the dilated bump has the stated fixed-support profile. -/
theorem broadPolarOperator_broadBump
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (R x : ℝ) :
    broadPolarOperator (broadBump φ R) x =
      (Real.sqrt R)⁻¹ * broadProfileNumerator φ (R⁻¹ ^ 2) (x / R) := by
  unfold broadPolarOperator broadBump broadProfileNumerator
  rw [secondDeriv_const_mul_comp_div φ hφ]
  ring

/-- Equation (30): exact actual broad-test energy after dilation. -/
theorem broadPolarOperator_broadBump_integral_sq
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x, broadPolarOperator (broadBump φ R) x ^ 2) =
      R⁻¹ ^ 4 * (∫ x, deriv (deriv φ) x ^ 2) +
      (R⁻¹ ^ 2 / 2) * (∫ x, deriv φ x ^ 2) +
      (1 / 16 : ℝ) * (∫ x, φ x ^ 2) := by
  simp_rw [broadPolarOperator_broadBump hφ R]
  rw [integral_sq_sqrt_dilate _ hR]
  unfold broadProfileNumerator
  rw [integral_sq_secondDeriv_sub_quarter hφ hc]
  ring

/-- Both exponential polar moments of the shifted second derivative vanish exactly. -/
theorem broadPolarOperator_polarMoments
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    (∫ x, Real.exp (x / 2) * broadPolarOperator v x) = 0 ∧
    (∫ x, Real.exp (-x / 2) * broadPolarOperator v x) = 0 := by
  constructor
  · simpa only [broadPolarOperator, one_div, div_eq_mul_inv, mul_comm, one_mul] using
      integral_exp_mul_secondDeriv_sub_quarter_eq_zero hv hc
        (c := (1 / 2 : ℝ)) (by norm_num)
  · simpa only [broadPolarOperator, neg_div, div_eq_mul_inv, neg_mul, mul_neg, mul_comm, one_mul] using
      integral_exp_mul_secondDeriv_sub_quarter_eq_zero hv hc
        (c := (-1 / 2 : ℝ)) (by norm_num)


/-- The profile normalizer is at least one quarter of the base bump's L² size. -/
theorem broadProfileNormalizer_lower
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (∫ x, φ x ^ 2) / 4 ≤ broadProfileNormalizer φ a := by
  calc
    _ = Real.sqrt ((1 / 16 : ℝ) * (∫ x, φ x ^ 2)) := by
      have hs : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      rw [Real.sqrt_mul (by norm_num), hs]
      ring
    _ ≤ _ := Real.sqrt_le_sqrt (integral_sq_secondDeriv_sub_quarter_lower hφ hc ha)

/-- Dilation preserves the C² regularity needed by the differential operator. -/
theorem broadBump_contDiff
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (R : ℝ) :
    ContDiff ℝ 2 (broadBump φ R) := by
  exact contDiff_const.mul (hφ.comp (contDiff_id.div_const R))

/-- A positive dilation preserves compact support. -/
theorem broadBump_hasCompactSupport
    {φ : ℝ → ℝ} (hc : HasCompactSupport φ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (broadBump φ R) := by
  have hdil : HasCompactSupport (fun x => φ (x / R)) := by
    simpa only [Function.comp_def, Homeomorph.mulRight₀_symm_apply, div_eq_mul_inv] using
      hc.comp_homeomorph (Homeomorph.mulRight₀ R (ne_of_gt hR)).symm
  exact hdil.mul_left

/-- The actual normalized broad test f_R = L(v_R)/N_R. -/
noncomputable def broadTest (φ : ℝ → ℝ) (R : ℝ) (x : ℝ) : ℝ :=
  broadPolarOperator (broadBump φ R) x / broadProfileNormalizer φ (R⁻¹ ^ 2)

/-- Equation (31): the actual normalized test is the square-root dilation of its profile. -/
theorem broadTest_eq_dilated_profile
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (R x : ℝ) :
    broadTest φ R x = (Real.sqrt R)⁻¹ *
      normalizedBroadProfile φ (R⁻¹ ^ 2) (x / R) := by
  unfold broadTest normalizedBroadProfile
  rw [broadPolarOperator_broadBump hφ]
  ring

/-- The actual normalized broad test has unit Lebesgue square integral. -/
theorem broadTest_integral_sq
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hI : (∫ x, φ x) ≠ 0) {R : ℝ} (hR : 0 < R) :
    (∫ x, broadTest φ R x ^ 2) = 1 := by
  simp_rw [broadTest_eq_dilated_profile hφ R]
  rw [integral_sq_sqrt_dilate _ hR]
  exact normalizedBroadProfile_integral_sq hφ hc hI (sq_nonneg _)

/-- Equation (29): both polar moments of the actual normalized broad test vanish. -/
theorem broadTest_polarMoments
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x, Real.exp (x / 2) * broadTest φ R x) = 0 ∧
    (∫ x, Real.exp (-x / 2) * broadTest φ R x) = 0 := by
  obtain ⟨hp, hm⟩ := broadPolarOperator_polarMoments
    (broadBump_contDiff hφ R) (broadBump_hasCompactSupport hc hR)
  simp only [broadTest, ← mul_div_assoc, integral_div, hp, hm, zero_div, and_self]


/-- Equation (32): the second-derivative contribution to the profile's mean vanishes. -/
theorem normalizedBroadProfile_integral
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (a : ℝ) :
    (∫ x, normalizedBroadProfile φ a x) =
      -(∫ x, φ x) / (4 * broadProfileNormalizer φ a) := by
  have h1 : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hi0 : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
  have hi2 : Integrable (deriv (deriv φ)) :=
    h1.continuous_deriv_one.integrable_of_hasCompactSupport hc.deriv.deriv
  have hzero : (∫ x, deriv (deriv φ) x) = 0 := by
    simpa using integral_exp_mul_secondDeriv_of_hasCompactSupport hφ hc 0
  unfold normalizedBroadProfile broadProfileNumerator
  rw [integral_div, integral_sub (hi2.const_mul a) (hi0.div_const 4),
    integral_const_mul, integral_div, hzero]
  ring


/-- The profile normalizer is exactly the Lebesgue L² size of the actual L(v_R). -/
theorem broadBump_normalizer_eq
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {R : ℝ} (hR : 0 < R) :
    Real.sqrt (∫ x, broadPolarOperator (broadBump φ R) x ^ 2) =
      broadProfileNormalizer φ (R⁻¹ ^ 2) := by
  simp_rw [broadPolarOperator_broadBump hφ R]
  rw [integral_sq_sqrt_dilate _ hR]
  rfl

end RiemannResearch.RH
