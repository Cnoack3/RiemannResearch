import RiemannResearch.Analysis.MontgomeryPrimeLogFourier
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Coeff.Abel
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.ClassicalStrongPNT
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeErrorStretched
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The centered first Mertens remainder in logarithmic coordinates

Abel summation retains the constant term as an absolutely convergent integral
of the relative Chebyshev error. The arithmetic input is the classical
quantitative prime number theorem, with the two logarithmic powers reserved
by `R_stretched_squareLog_bound_of_medium_rpow`.
-/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set
open RiemannResearch.NumberTheory.PrimeNumberTheorem
open scoped Topology BigOperators ArithmeticFunction

def logPsiError (y : ℝ) : ℝ := Chebyshev.psi (Real.exp y) / Real.exp y - 1

private theorem measurable_logPsiError : Measurable logPsiError :=
  ((Chebyshev.psi_mono.measurable.comp Real.continuous_exp.measurable).div
    Real.continuous_exp.measurable).sub measurable_const

/-- A global bound retaining both the exponential decay and the integrable factor. -/
theorem logPsiError_stretched :
    ∃ a > (0 : ℝ), ∃ D > (0 : ℝ), ∀ y : ℝ, 0 ≤ y →
      |logPsiError y| ≤ D * Real.exp (-a * Real.sqrt y) / (1 + y) ^ 2 := by
  obtain ⟨a, ha, D, hD, hb⟩ := R_stretched_squareLog_bound_of_medium_rpow
    (1 / 2) (by norm_num) Quantitative.ClassicalRegion.StrongPNT
  refine ⟨a, ha, D, hD, fun y hy => ?_⟩
  have h := hb (Real.exp y) (Real.one_le_exp hy)
  change |Chebyshev.psi (Real.exp y) - Real.exp y| ≤ D * Real.exp y *
    Real.exp (-a * (Real.log (Real.exp y)) ^ (1 / 2 : ℝ)) /
    (1 + Real.log (Real.exp y)) ^ 2 at h
  rw [Real.log_exp, ← Real.sqrt_eq_rpow] at h
  rw [logPsiError, show Chebyshev.psi (Real.exp y) / Real.exp y - 1 =
      (Chebyshev.psi (Real.exp y) - Real.exp y) / Real.exp y by field_simp,
    abs_div, abs_of_pos (Real.exp_pos y)]
  apply (div_le_iff₀ (Real.exp_pos y)).2
  exact h.trans_eq (by ring)

private def invSqProfile (y : ℝ) : ℝ := ((1 + y)^2)⁻¹

private theorem invSqProfile_deriv {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (fun z : ℝ => -(1 + z)⁻¹) (invSqProfile y) y := by
  have hn : 1 + y ≠ 0 := by linarith
  have hd : HasDerivAt (fun z : ℝ => 1 + z) 1 y := (hasDerivAt_id y).const_add 1
  have hd' := (hd.inv hn).neg
  change HasDerivAt (fun z : ℝ => -(1+z)⁻¹) (-(-1 / (1+y)^2)) y at hd'
  simpa only [neg_div, neg_neg, one_div, invSqProfile] using hd'

private theorem tendsto_invProfile :
    Tendsto (fun y : ℝ => -(1 + y)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => 1 + y) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 tendsto_id
  have hh := h.inv_tendsto_atTop.neg
  change Tendsto (fun y : ℝ => -(1+y)⁻¹) atTop (𝓝 (-0)) at hh
  simpa only [neg_zero] using hh

private theorem invSqProfile_integrable {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn invSqProfile (Ioi y) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := fun z : ℝ => -(1 + z)⁻¹)
    (l := 0) _ _ tendsto_invProfile
  · intro t ht
    exact invSqProfile_deriv (hy.trans ht)
  · intro t _
    exact inv_nonneg.mpr (sq_nonneg _)

private theorem invSqProfile_integral {y : ℝ} (hy : 0 ≤ y) :
    (∫ t in Ioi y, invSqProfile t) = (1 + y)⁻¹ := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t (ht : t ∈ Ici y) => invSqProfile_deriv (hy.trans ht))
    (invSqProfile_integrable hy) tendsto_invProfile
  simpa only [zero_sub, neg_neg] using h

private theorem exp_sqrt_antitone {a : ℝ} (ha : 0 ≤ a) {s t : ℝ} (hst : s ≤ t) :
    Real.exp (-a * Real.sqrt t) ≤ Real.exp (-a * Real.sqrt s) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt hst) (neg_nonpos.mpr ha))

private theorem logPsiError_majorant {a D : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hb : ∀ t : ℝ, 0 ≤ t →
      |logPsiError t| ≤ D * Real.exp (-a * Real.sqrt t) / (1 + t)^2)
    {y t : ℝ} (hy : 0 ≤ y) (ht : y ≤ t) :
    |logPsiError t| ≤ (D * Real.exp (-a * Real.sqrt y)) * invSqProfile t := by
  refine (hb t (hy.trans ht)).trans ?_
  rw [div_eq_mul_inv, invSqProfile]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (exp_sqrt_antitone ha ht) hD) (by positivity)

theorem integrableOn_logPsiError : IntegrableOn logPsiError (Ioi 0) := by
  obtain ⟨a, ha, D, hD, h⟩ := logPsiError_stretched
  apply ((invSqProfile_integrable (le_refl (0 : ℝ))).const_mul
    (D * Real.exp (-a * Real.sqrt 0))).mono' measurable_logPsiError.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs] using logPsiError_majorant ha.le hD.le h (le_refl 0) ht.le

/-- The constant singled out by absolute convergence of the relative-PNT integral. -/
def mertensCenter : ℝ := 1 + ∫ y in Ioi 0, logPsiError y

def logMertensRemainder (y : ℝ) : ℝ := Zeta23.XiPrime.Mfun (Real.exp y) - y - mertensCenter

theorem measurable_logMertensRemainder : Measurable logMertensRemainder :=
  ((Zeta23.XiPrime.Mfun_mono.measurable.comp Real.continuous_exp.measurable).sub
    measurable_id).sub measurable_const

/-- Partial summation in logarithmic coordinates with the inclusive upper endpoint. -/
theorem mertens_log_abel {y : ℝ} (hy : 0 ≤ y) :
    Zeta23.XiPrime.Mfun (Real.exp y) - y =
      1 + logPsiError y + ∫ t in Set.Ioc 0 y, logPsiError t := by
  let x := Real.exp y
  have hx : 1 ≤ x := Real.one_le_exp hy
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t :=
    fun t ht => (hasDerivAt_inv (lt_of_lt_of_le zero_lt_one ht.1).ne').differentiableAt
  have hint : IntegrableOn (deriv fun t : ℝ => t⁻¹) (Set.Icc 1 x) := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    exact ((continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (lt_of_lt_of_le zero_lt_one ht.1).ne')).neg
  have h := sum_mul_eq_sub_integral_mul₀ (fun n => ArithmeticFunction.vonMangoldt n)
    (by simp) x hdiff hint
  have hpsi (t : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi t := by
    rw [Zeta23.XiPrime.sum_Icc_eq_sum_Ioc' (by simp)]
    rfl
  have hsum : (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (k : ℝ)⁻¹ * ArithmeticFunction.vonMangoldt k) =
      Zeta23.XiPrime.Mfun x := by
    unfold Zeta23.XiPrime.Mfun
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [hsum, hpsi, deriv_inv, neg_mul, integral_neg, sub_neg_eq_add] at h
  have hch := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := y) (f := Real.exp) (f' := Real.exp)
    (g := fun t : ℝ => (t ^ 2)⁻¹ * Chebyshev.psi t)
    Real.continuous_exp.continuousOn (fun t _ => Real.hasDerivAt_exp t)
    (fun t _ => (Real.exp_pos t).le)
  rw [Real.exp_zero, intervalIntegral.integral_of_le hy,
    intervalIntegral.integral_of_le hx] at hch
  have he : (∫ t in Set.Ioc (0 : ℝ) y,
      ((fun z : ℝ => (z ^ 2)⁻¹ * Chebyshev.psi z) ∘ Real.exp) t * Real.exp t) =
      ∫ t in Set.Ioc 0 y, Chebyshev.psi (Real.exp t) / Real.exp t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp only [Function.comp_apply]
    field_simp [(Real.exp_pos t).ne']
  rw [he] at hch
  have hi : IntervalIntegrable (fun t : ℝ => Chebyshev.psi (Real.exp t) / Real.exp t)
      volume 0 y := by
    have hi' : IntervalIntegrable (fun t => Chebyshev.psi (Real.exp t)) volume 0 y :=
      (Chebyshev.psi_mono.comp Real.exp_strictMono.monotone).intervalIntegrable
    have hc : Continuous (fun t : ℝ => (Real.exp t)⁻¹) := by
      simpa only [Function.comp_def, Real.exp_neg] using Real.continuous_exp.comp continuous_neg
    simpa only [div_eq_mul_inv] using hi'.mul_continuousOn hc.continuousOn
  have hioc := (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mp hi
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 y) :=
    integrableOn_const (by simp)
  have hconst : (∫ t in Set.Ioc 0 y, (1 : ℝ)) = y := by
    rw [← intervalIntegral.integral_of_le hy, intervalIntegral.integral_const]
    simp
  have hi1 : (∫ t in Set.Ioc 0 y, logPsiError t) =
      (∫ t in Set.Ioc 0 y, Chebyshev.psi (Real.exp t) / Real.exp t) - y := by
    exact (integral_sub hioc hone).trans (by rw [hconst])
  rw [hi1]
  change Zeta23.XiPrime.Mfun x - y =
    1 + (Chebyshev.psi x / x - 1) + ((∫ t in Set.Ioc 0 y, _) - y)
  rw [h, hch]
  ring



theorem logMertensRemainder_eq {y : ℝ} (hy : 0 ≤ y) :
    logMertensRemainder y = logPsiError y - ∫ t in Ioi y, logPsiError t := by
  have h := integrableOn_logPsiError
  have hsplit : (∫ t in Ioi 0, logPsiError t) =
      (∫ t in Ioc 0 y, logPsiError t) + ∫ t in Ioi y, logPsiError t := by
    rw [← setIntegral_union ?_ measurableSet_Ioi (h.mono_set Ioc_subset_Ioi_self)
      (h.mono_set (Ioi_subset_Ioi hy)), Ioc_union_Ioi_eq_Ioi hy]
    exact Set.disjoint_left.mpr fun t ht ht' => (not_lt.mpr ht.2) ht'
  rw [logMertensRemainder, mertens_log_abel hy, mertensCenter, hsplit]
  ring

theorem logMertensRemainder_stretched :
    ∃ a > (0 : ℝ), ∃ K > (0 : ℝ), ∀ y : ℝ, 0 ≤ y →
      |logMertensRemainder y| ≤ K * Real.exp (-a * Real.sqrt y) / (1+y) := by
  obtain ⟨a, ha, D, hD, h⟩ := logPsiError_stretched
  refine ⟨a, ha, 2*D, by positivity, fun y hy => ?_⟩
  let E := D * Real.exp (-a * Real.sqrt y)
  have hE : 0 ≤ E := mul_nonneg hD.le (Real.exp_pos _).le
  have hi := integrableOn_logPsiError.mono_set (Ioi_subset_Ioi hy)
  have htail : |∫ t in Ioi y, logPsiError t| ≤ E / (1+y) := by
    calc
      _ ≤ ∫ t in Ioi y, |logPsiError t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioi y, E * invSqProfile t := by
        apply integral_mono_ae hi.abs ((invSqProfile_integrable hy).const_mul E)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact logPsiError_majorant ha.le hD.le h hy ht.le
      _ = _ := by rw [integral_const_mul, invSqProfile_integral hy, div_eq_mul_inv]
  have hpoint : |logPsiError y| ≤ E / (1+y) := by
    exact (h y hy).trans (div_le_div_of_nonneg_left hE (by linarith) (by nlinarith [sq_nonneg y]))
  rw [logMertensRemainder_eq hy]
  exact (abs_sub _ _).trans ((add_le_add hpoint htail).trans_eq (by dsimp [E]; ring))

private theorem exp_sqrt_le_one {a y : ℝ} (ha : 0 ≤ a) :
    Real.exp (-a * Real.sqrt y) ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Real.sqrt_nonneg _))

private theorem logMertensRemainder_inverse :
    ∃ K > (0 : ℝ), ∀ y : ℝ, 0 ≤ y → |logMertensRemainder y| ≤ K / (1+y) := by
  obtain ⟨a, ha, K, hK, h⟩ := logMertensRemainder_stretched
  refine ⟨K, hK, fun y hy => (h y hy).trans ?_⟩
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hK.le (exp_sqrt_le_one ha.le))
    (by linarith)

/-- The centered first Mertens sum has a square-integrable logarithmic remainder. -/
theorem integrableOn_logMertensRemainder_sq :
    IntegrableOn (fun y => logMertensRemainder y ^ 2) (Ioi 0) := by
  obtain ⟨K, hK, h⟩ := logMertensRemainder_inverse
  apply ((invSqProfile_integrable (le_refl (0 : ℝ))).const_mul (K^2)).mono'
    ((measurable_logMertensRemainder.pow_const 2).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hb := pow_le_pow_left₀ (abs_nonneg _) (h y hy.le) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (logMertensRemainder y))]
  rw [sq_abs, div_pow, div_eq_mul_inv] at hb
  exact hb

theorem tendsto_logMertensRemainder : Tendsto logMertensRemainder atTop (𝓝 0) := by
  obtain ⟨K, _, h⟩ := logMertensRemainder_inverse
  have hlim : Tendsto (fun y : ℝ => K / (1 + y)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  exact h y hy

theorem mertens_centered_asymptotic :
    Tendsto (fun x : ℝ => Zeta23.XiPrime.Mfun x - Real.log x) atTop (𝓝 mertensCenter) := by
  have h := (tendsto_logMertensRemainder.comp Real.tendsto_log_atTop).add_const mertensCenter
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [logMertensRemainder, Real.exp_log hx]

theorem primeLogCDF_sub_eq_centered {T : ℝ} (hT : 1 < T) (v : ℝ) :
    primeLogCDF T v - v = (mertensCenter + logMertensRemainder (Real.log T * v)) / Real.log T := by
  have hL := Real.log_pos hT
  rw [logMertensRemainder, Zeta23.XiPrime.Mfun_eq_Ioc, primeLogCDF,
    Real.rpow_def_of_pos (zero_lt_one.trans hT)]
  field_simp [hL.ne'] <;> ring

/-- A summable, monotone envelope for the local supremum on every unit log block. -/
theorem logMertensRemainder_inverse_square :
    ∃ D > (0 : ℝ), ∀ y : ℝ, 0 ≤ y → |logMertensRemainder y| ≤ D / (1+y)^2 := by
  obtain ⟨a, ha, K, hK, hb⟩ := logMertensRemainder_stretched
  refine ⟨K * (1+2/a^2), by positivity, fun y hy => ?_⟩
  have hsq : 0 < a^2 := sq_pos_of_pos ha
  have hpos : 0 < 1+y := by linarith
  have hu : 0 ≤ a * Real.sqrt y := mul_nonneg ha.le (Real.sqrt_nonneg _)
  have hfac := Real.pow_div_factorial_le_exp (a * Real.sqrt y) hu 2
  rw [mul_pow, Real.sq_sqrt hy] at hfac
  norm_num at hfac
  have h1 : y ≤ (2/a^2) * Real.exp (a*Real.sqrt y) := by
    calc
      _ ≤ (2 * Real.exp (a*Real.sqrt y)) / a^2 :=
        (le_div_iff₀ hsq).2 (by nlinarith only [hfac])
      _ = _ := by ring
  have he : 1+y ≤ (1+2/a^2)*Real.exp (a*Real.sqrt y) := by
    rw [add_mul, one_mul]
    exact add_le_add (Real.one_le_exp hu) h1
  have he' : (1+y)*Real.exp (-a*Real.sqrt y) ≤ 1+2/a^2 := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos _)).2 he
  refine (hb y hy).trans ?_
  apply (div_le_div_iff₀ hpos (sq_pos_of_pos hpos)).2
  calc
    _ = K * ((1+y)*Real.exp (-a*Real.sqrt y)) * (1+y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he' hK.le) hpos.le

theorem integrableOn_logMertensRemainder :
    IntegrableOn logMertensRemainder (Ioi 0) := by
  obtain ⟨D, _, h⟩ := logMertensRemainder_inverse_square
  apply ((invSqProfile_integrable (le_refl (0 : ℝ))).const_mul D).mono'
    measurable_logMertensRemainder.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simpa only [Real.norm_eq_abs, div_eq_mul_inv, invSqProfile] using h y hy.le

theorem logMertensRemainder_summable_envelope :
    ∃ b : ℕ → ℝ, Summable b ∧ (∀ j, 0 ≤ b j) ∧
      ∀ (j : ℕ) (y : ℝ), (j : ℝ) ≤ y → |logMertensRemainder y| ≤ b j := by
  obtain ⟨D, hD, h⟩ := logMertensRemainder_inverse_square
  refine ⟨fun j => D / (1+(j : ℝ))^2, ?_, fun j => by positivity, fun j y hj => ?_⟩
  · have hs := (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, add_comm] using hs.mul_left D
  · have hy := (Nat.cast_nonneg j).trans hj
    exact (h y hy).trans (div_le_div_of_nonneg_left hD.le (by positivity)
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + (j : ℝ) ≤ 1 + y) 2))


/-- A common inverse-power majorant for every point and for the integral on a log tail.
The factor `z^5` lets the angular frequency grow as `z^4`. -/
theorem logMertensRemainder_fifth_tail :
    ∃ K > (0 : ℝ), ∀ {z L : ℝ}, 1 ≤ z → z ≤ L →
      |logMertensRemainder L| ≤ K / z^5 ∧
      (∫ y in z..L, |logMertensRemainder y|) ≤ K / z^5 := by
  obtain ⟨a, ha, C, hC, hr⟩ := logMertensRemainder_stretched
  let k : ℝ := (Nat.factorial 12 : ℝ) / a^12
  let K : ℝ := 2*C*k
  have hk : 0 < k := by dsimp [k]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun {z L} hz hzL => ?_⟩
  have hz0 : 0 < z := by linarith
  have major {y : ℝ} (hy : z ≤ y) :
      |logMertensRemainder y| ≤ (K/z^5) * invSqProfile y := by
    have hy0 : 0 ≤ y := by linarith
    have he := Real.pow_div_factorial_le_exp (a*Real.sqrt y) (by positivity) 12
    have hs : Real.sqrt y ^ 12 = y^6 := by
      rw [show (12 : ℕ) = 2*6 by decide, pow_mul, Real.sq_sqrt hy0]
    rw [mul_pow, hs] at he
    have hy6 : y^6 ≤ k * Real.exp (a*Real.sqrt y) := by
      dsimp [k]
      have hf : (0:ℝ) < (Nat.factorial 12 : ℝ) := by positivity
      have he' := (div_le_iff₀ hf).1 he
      field_simp [ha.ne']
      linarith
    have hzy : z^5 * (1+y) ≤ 2*y^6 := calc
      _ ≤ y^5 * (2*y) := mul_le_mul (pow_le_pow_left₀ hz0.le hy 5)
        (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
    have hprod : z^5 * (1+y) * Real.exp (-a*Real.sqrt y) ≤ 2*k := by
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
      exact (div_le_iff₀ (Real.exp_pos _)).2 (by linarith)
    refine (hr y hy0).trans ?_
    dsimp [invSqProfile, K]
    rw [← div_eq_mul_inv]
    have h1 : 0 < 1+y := by linarith
    field_simp [h1.ne', hz0.ne']
    rw [neg_mul] at hprod
    nlinarith only [hprod]
  constructor
  · refine (major hzL).trans (mul_le_of_le_one_right (by positivity) ?_)
    dsimp [invSqProfile]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg L])
  · rw [intervalIntegral.integral_of_le hzL]
    have hj := (integrableOn_logMertensRemainder.mono_set
      (show Ioc z L ⊆ Ioi 0 from fun _ hx => hz0.trans hx.1)).abs
    have hi : IntegrableOn (fun y => (K/z^5)*invSqProfile y) (Ioi z) :=
      (invSqProfile_integrable hz0.le).const_mul (K/z^5)
    calc
      _ ≤ ∫ y in Ioc z L, (K/z^5)*invSqProfile y := by
        apply integral_mono_ae hj (hi.mono_set Ioc_subset_Ioi_self)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact major hy.1.le
      _ ≤ ∫ y in Ioi z, (K/z^5)*invSqProfile y :=
        setIntegral_mono_set hi (Eventually.of_forall fun y => by dsimp [invSqProfile]; positivity)
          (Eventually.of_forall fun _ h => h.1)
      _ ≤ _ := by
        rw [integral_const_mul, invSqProfile_integral hz0.le]
        apply mul_le_of_le_one_right (by positivity)
        exact inv_le_one_of_one_le₀ (by linarith)

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.logMertensRemainder_fifth_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms logMertensRemainder_fifth_tail

end RiemannResearch.Analysis.MontgomeryPrimeTrace
