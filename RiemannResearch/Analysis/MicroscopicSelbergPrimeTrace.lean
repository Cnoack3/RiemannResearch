import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroDiscrepancy
import RiemannResearch.Analysis.MontgomeryOrdinateSineTrace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Complete Selberg windows and short-prime covariance

The complete windows include one integral for each actual occurrence, with the
upper and lower origins left unclipped. The difference from the covariance with
the actual discrepancy therefore includes both the endpoint and smooth terms.
See sections 1 and 2 of `RIEMANN_MICROSCOPIC_SELBERG_TRACE_20261125.md`. -/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MicroscopicSelbergPrimeTrace
open ActualZeroOrdinate ActualZeroDiscrepancy MontgomeryOrdinateSineTrace

/-- The coefficient of the real ordinate sum in a complete, height-normalized
Selberg window. The minus sign of the prime polynomial is kept separately. -/
def traceWeight (T h : ℝ) (p : ℕ) : ℝ :=
  2 * (1 - Real.cos (h * Real.log p)) /
    (Real.pi * T * Real.sqrt p * Real.log p)

/-- The Selberg sine polynomial for any finite prime dictionary. -/
def polynomial (s : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ s, (-(Real.pi * Real.sqrt p)⁻¹) * Real.sin (t * Real.log p)

private theorem continuous_polynomial (s : Finset ℕ) : Continuous (polynomial s) := by
  unfold polynomial
  fun_prop

/-- Complete translated windows, repeated with the true analytic multiplicities. -/
def completeWindows (T h : ℝ) (s : Finset ℕ) : ℝ :=
  (∑ c : Copies T, ∫ t in (c.1.1.im - h)..c.1.1.im,
    polynomial s (t + h) - polynomial s t) / T

private theorem ordinateSum_re_eq_copies (T a : ℝ) :
    (ordinateSum T a).re = ∑ c : Copies T, Real.cos (c.1.1.im * a) := by
  rw [ordinateSum, sum_eq_copies, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp [ZeroOrdinate.phase, Complex.exp_re, mul_comm]

/-- An exact finite Selberg trace with no boundary approximation. -/
theorem completeWindows_eq_ordinate (T h : ℝ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, 1 < p) :
    completeWindows T h s =
      -∑ p ∈ s, traceWeight T h p * (ordinateSum T (Real.log p)).re := by
  classical
  have hi (c : Copies T) :
      (∫ t in (c.1.1.im - h)..c.1.1.im,
        polynomial s (t + h) - polynomial s t) =
      ∑ p ∈ s, (-(Real.pi * Real.sqrt p)⁻¹) *
        (2 * (1 - Real.cos (h * Real.log p)) *
        Real.cos (c.1.1.im * Real.log p) / Real.log p) := by
    simp only [polynomial, ← Finset.sum_sub_distrib, ← mul_sub]
    apply ordinate_weighted_sine_increment_integral
    intro p hp
    exact (Real.log_pos (by exact_mod_cast hs p hp)).ne'
  simp_rw [completeWindows, hi]
  rw [Finset.sum_comm, Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ordinateSum_re_eq_copies, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  simp only [traceWeight, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The signed horizontal trace, evaluated at the prime frequencies. -/
def horizontalTrace (T h : ℝ) (s : Finset ℕ) : ℝ :=
  ∑ p ∈ s, traceWeight T h p * (coshCorrection T (Real.log p)).re

/-- Landau's diagonal in the rational-frequency normalization of the repository. -/
def primeDiagonal (T h : ℝ) (s : Finset ℕ) : ℝ :=
  ∑ p ∈ s, traceWeight T h p * (T * rationalLandauMain p 1)

/-- On actual primes the diagonal is the classical cosine sum. -/
theorem primeDiagonal_eq_cosine (T h : ℝ) (s : Finset ℕ) (hT : T ≠ 0)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    primeDiagonal T h s = ∑ p ∈ s, (1 - Real.cos (h * Real.log p)) / (Real.pi ^ 2 * p) := by
  unfold primeDiagonal
  apply Finset.sum_congr rfl
  intro p hp
  have hgt := (hs p hp).one_lt
  have hpos : 0 < (p : ℝ) := by exact_mod_cast (hs p hp).pos
  have hlog := Real.log_pos (show 1 < (p : ℝ) by exact_mod_cast hgt)
  have hsqrt := Real.sqrt_pos.mpr hpos
  rw [rationalLandauMain_eq_vonMangoldt_div_sqrt (by decide) hgt]
  simp only [one_dvd, if_true, Nat.div_one, Nat.cast_one, div_one,
    ArithmeticFunction.vonMangoldt_apply_prime (hs p hp), traceWeight]
  field_simp [hT, Real.pi_ne_zero, hsqrt.ne', hlog.ne', hpos.ne']
  ring_nf
  rw [Real.sq_sqrt hpos.le]

private theorem cosine_quadratic_error (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x ^ 2 / 2 - (1 - Real.cos x) ∧
      x ^ 2 / 2 - (1 - Real.cos x) ≤ x ^ 4 / 24 := by
  let u := x / 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have habs : |Real.sin u| ≤ u := by simpa only [abs_of_nonneg hu] using
    (Real.abs_sin_le_abs (x := u))
  have h1 : u - Real.sin u ≤ u^3 / 6 := by linarith [Real.sin_ge_sub_cube hu]
  have h2 : u + Real.sin u ≤ 2*u := by linarith [(abs_le.mp habs).2]
  have hm := mul_le_mul h1 h2 (by linarith [(abs_le.mp habs).1]) (by positivity)
  have hi := Real.sin_sq_eq_half_sub u
  have he : 2*u = x := by dsimp [u]; ring
  rw [he] at hi
  constructor
  · linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  · dsimp [u] at hm hi
    nlinarith only [hm, hi]

/-- The finite short-prime diagonal has a one-sided fourth-order error, uniform
in the dictionary, height and physical width. -/
theorem primeDiagonal_quadratic_error (T h : ℝ) (s : Finset ℕ) (hT : T ≠ 0)
    (hh : 0 ≤ h) (hs : ∀ p ∈ s, Nat.Prime p) :
    let main := ∑ p ∈ s, ((h * Real.log p)^2 / 2) / (Real.pi^2 * p)
    0 ≤ main - primeDiagonal T h s ∧
      main - primeDiagonal T h s ≤ ∑ p ∈ s, ((h * Real.log p)^4 / 24) / (Real.pi^2 * p) := by
  dsimp only
  rw [primeDiagonal_eq_cosine T h s hT hs, ← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    rw [← sub_div]
    exact div_nonneg (cosine_quadratic_error _ (mul_nonneg hh
      (Real.log_nonneg (by exact_mod_cast (hs p hp).one_le)))).1 (by positivity)
  · apply Finset.sum_le_sum
    intro p hp
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (cosine_quadratic_error _ (mul_nonneg hh
      (Real.log_nonneg (by exact_mod_cast (hs p hp).one_le)))).2 (by positivity)

/-- Exact error after removal of the prime diagonal and the signed horizontal
trace. The residual is a weighted sum of actual Landau errors, at all cutoffs. -/
theorem completeWindows_sub_diagonal_horizontal (T h : ℝ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, 1 < p) :
    completeWindows T h s - primeDiagonal T h s - horizontalTrace T h s =
      -∑ p ∈ s, traceWeight T h p *
        (landauSum T (Real.log p) + (T * rationalLandauMain p 1 : ℝ)).re := by
  rw [completeWindows_eq_ordinate T h s hs]
  simp only [primeDiagonal, horizontalTrace, exact_signed_correction, Complex.sub_re,
    Complex.add_re, Complex.ofReal_re, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring

/-- An unconditional cutoff-uniform Landau error bound. The displayed
polynomial dependence is intended for short prime dictionaries. -/
theorem exists_completeWindows_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T X h : ℝ) (s : Finset ℕ), 9 ≤ T →
      (∀ p ∈ s, 1 < p ∧ (p : ℝ) ≤ X) →
      |completeWindows T h s - primeDiagonal T h s - horizontalTrace T h s| ≤
        (∑ p ∈ s, |traceWeight T h p|) *
        (C * (X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 +
          X * Real.log (T + 3))) := by
  obtain ⟨C, hC, hlandau⟩ := exists_uniform_rational_landau_rpow_bound
  refine ⟨C, hC, ?_⟩
  intro T X h s hT hs
  rw [completeWindows_sub_diagonal_horizontal T h s (fun p hp => (hs p hp).1), abs_neg,
    Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (Complex.abs_re_le_norm _).trans
  simpa only [Nat.cast_one, div_one] using
    hlandau T X p 1 hT (by decide) (hs p hp).1 (hs p hp).2

/-- The actual rational ordinate estimate also controls the *combined*
horizontal and Landau errors without assuming a density estimate. The bound
is simultaneous in the physical width and the moving dictionary. -/
theorem eventually_completeWindows_sub_primeDiagonal_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ (h : ℝ) (s : Finset ℕ),
      (∀ p ∈ s, 1 < p) →
      |completeWindows T h s - primeDiagonal T h s| ≤
        ∑ p ∈ s, |T * traceWeight T h p| *
          ((K * horizontalLogRate T) * (1 + Real.log p)^2) := by
  obtain ⟨K, hK, hb⟩ := eventually_rational_ordinate_remainder_loglog
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with T hbT hT
  intro h s hs
  have he : completeWindows T h s - primeDiagonal T h s =
      -∑ p ∈ s, (T * traceWeight T h p) *
        ((ordinateSum T (Real.log p)).re / T + rationalLandauMain p 1) := by
    rw [completeWindows_eq_ordinate T h s hs]
    unfold primeDiagonal
    rw [show ∀ a b : ℝ, -a - b = -(a+b) by intros; ring, ← Finset.sum_add_distrib]
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro p hp
    field_simp [hT.ne']
  rw [he, abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hv := (Complex.abs_re_le_norm _).trans (hbT p 1 (by decide) (hs p hp))
  simpa only [Nat.cast_one, div_one, Complex.add_re, Complex.div_ofReal_re,
    Complex.ofReal_re] using hv

private theorem height_weight_le {T h : ℝ} {p : ℕ} (hT : 0 < T) (hp : 1 < p) :
    |T * traceWeight T h p| ≤ h^2 * (Real.log p / (Real.pi * Real.sqrt p)) := by
  have hlog := Real.log_pos (show 1 < (p : ℝ) by exact_mod_cast hp)
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hp
  have hr := Real.sqrt_pos.mpr hp0
  have he : T * traceWeight T h p =
      2*(1-Real.cos (h*Real.log p))/(Real.pi*Real.sqrt p*Real.log p) := by
    unfold traceWeight
    field_simp [hT.ne', Real.pi_ne_zero, hr.ne', hlog.ne']
  rw [he, abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num)
    (sub_nonneg.mpr (Real.cos_le_one _))) (by positivity))]
  calc
    _ ≤ (h*Real.log p)^2 / (Real.pi*Real.sqrt p*Real.log p) :=
      div_le_div_of_nonneg_right (by linarith
        [Real.one_sub_sq_div_two_le_cos (x := h*Real.log p)]) (by positivity)
    _ = _ := by field_simp [hr.ne', hlog.ne', Real.pi_ne_zero]

/-- A sufficient growing-dictionary condition for normalized complete-window
covariance asymptotics. The width can approach zero arbitrarily quickly. -/
theorem completeWindows_normalized_tendsto (s : ℝ → Finset ℕ) (h : ℝ → ℝ)
    (hs : ∀ᶠ T : ℝ in atTop, ∀ p ∈ s T, 1 < p)
    (hh : ∀ᶠ T : ℝ in atTop, h T ≠ 0)
    (hb : Filter.Tendsto (fun T : ℝ => horizontalLogRate T *
        ∑ p ∈ s T, (Real.log p / (Real.pi * Real.sqrt p)) * (1 + Real.log p)^2)
      atTop (𝓝 0)) :
    Filter.Tendsto (fun T : ℝ =>
      (completeWindows T (h T) (s T) - primeDiagonal T (h T) (s T)) / (h T)^2)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := eventually_completeWindows_sub_primeDiagonal_le
  have hlim := hb.const_mul K
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hs, hh, hbound, eventually_gt_atTop (1 : ℝ)] with T hsT hhT hBT hT
  have hr : 0 ≤ horizontalLogRate T := by
    exact div_nonneg (sq_nonneg _) (Real.log_pos hT).le
  have ht : 0 < T := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg (h T))]
  apply (div_le_iff₀ (sq_pos_of_ne_zero hhT)).2
  apply (hBT (h T) (s T) hsT).trans
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  calc
    _ ≤ ((h T)^2 * (Real.log p / (Real.pi * Real.sqrt p))) *
        (K * horizontalLogRate T * (1 + Real.log p)^2) :=
      mul_le_mul_of_nonneg_right (height_weight_le ht (hsT p hp)) (by positivity)
    _ = _ := by ring

/-- Height-normalized pairing of physical forward increments. -/
def incrementCovariance (T h : ℝ) (f g : ℝ → ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, (f (t + h) - f t) * (g (t + h) - g t)) / T

/-- Exact subtraction for the true discrepancy and a short Selberg polynomial,
with integrability discharged at every real height and width. -/
theorem remainder_covariance_eq_sub (T h : ℝ) (full short : Finset ℕ) :
    incrementCovariance T h (fun t => discrepancy t - polynomial full t) (polynomial short) =
      incrementCovariance T h discrepancy (polynomial short) -
      incrementCovariance T h (polynomial full) (polynomial short) := by
  let g := fun t : ℝ => polynomial short (t + h) - polynomial short t
  have hg : Continuous g := ((continuous_polynomial short).comp
    (continuous_id.add continuous_const)).sub (continuous_polynomial short)
  have hf : Continuous (fun t : ℝ => polynomial full (t+h) - polynomial full t) :=
    ((continuous_polynomial full).comp (continuous_id.add continuous_const)).sub
      (continuous_polynomial full)
  have hd : IntervalIntegrable (fun t : ℝ => discrepancy (t+h) - discrepancy t)
      volume 0 T :=
    (show IntervalIntegrable (fun t : ℝ => discrepancy (t+h)) volume 0 T by
      simpa only [sub_self, add_sub_cancel_right] using
        (discrepancy_intervalIntegrable h (T+h)).comp_add_right h).sub
      (discrepancy_intervalIntegrable 0 T)
  have hid := intervalIntegral.integral_sub (hd.mul_continuousOn hg.continuousOn)
    ((hf.mul hg).intervalIntegrable _ _)
  simp only [Pi.mul_apply, g] at hid
  unfold incrementCovariance
  rw [← sub_div, ← hid]
  apply congrArg (fun x : ℝ => x / T)
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [g]
  ring

/-- The mixed discrepancy–polynomial pairing retains each of the three signed
errors: cutoff and smooth drift, the Landau residual, and the prime mean value.
These are the three estimates needed to pass to the full-cutoff limit. -/
theorem mixed_covariance_sub_horizontal (T h : ℝ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, 1 < p) :
    incrementCovariance T h (fun t => discrepancy t - polynomial s t) (polynomial s) -
      horizontalTrace T h s =
      (incrementCovariance T h discrepancy (polynomial s) - completeWindows T h s) -
      (∑ p ∈ s, traceWeight T h p *
        (landauSum T (Real.log p) + (T * rationalLandauMain p 1 : ℝ)).re) -
      (incrementCovariance T h (polynomial s) (polynomial s) - primeDiagonal T h s) := by
  rw [remainder_covariance_eq_sub]
  linarith only [completeWindows_sub_diagonal_horizontal T h s hs]

/-- Any common-diagonal error budgets for the two measured covariances give
a short-prime orthogonality bound with the sum of the two constants. -/
theorem abs_remainder_covariance_le (T h D eS eX : ℝ) (full short : Finset ℕ)
    (hS : |incrementCovariance T h discrepancy (polynomial short) - D| ≤ eS)
    (hX : |incrementCovariance T h (polynomial full) (polynomial short) - D| ≤ eX) :
    |incrementCovariance T h (fun t => discrepancy t - polynomial full t) (polynomial short)| ≤
      eS + eX := by
  rw [remainder_covariance_eq_sub]
  simpa only [sub_sub_sub_cancel_right] using
    (abs_sub _ _).trans (add_le_add hS hX)


/-- Every prime through the integer part of the physical log-log cutoff. -/
def loglogPrimes (T : ℝ) : Finset ℕ :=
  (Nat.floor (Real.log (Real.log T)) + 1).primesBelow

/-- The normalized complete-window covariance converges to its prime diagonal
for all primes through log log T, simultaneously along any nonzero moving width. -/
theorem completeWindows_loglogPrimes_tendsto (h : ℝ → ℝ) (hh : ∀ᶠ T : ℝ in atTop, h T ≠ 0) :
    Tendsto (fun T : ℝ =>
      (completeWindows T (h T) (loglogPrimes T) - primeDiagonal T (h T) (loglogPrimes T)) /
        (h T)^2) atTop (𝓝 0) := by
  apply completeWindows_normalized_tendsto
  · exact Filter.Eventually.of_forall (fun T p hp => (Nat.mem_primesBelow.mp hp).2.one_lt)
  · exact hh
  have hlim : Tendsto (fun T : ℝ => 8 * ((Real.log (Real.log T))^6 / Real.log T))
      atTop (𝓝 0) := by
    have hl := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).comp
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)).const_mul (8 : ℝ)
    rw [mul_zero] at hl
    apply hl.congr'
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT
    simp only [Function.comp_def, Real.exp_neg, Real.exp_log hT, div_eq_mul_inv]
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    apply mul_nonneg (div_nonneg (sq_nonneg _) (Real.log_pos hT).le)
    apply Finset.sum_nonneg
    intro p hp
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_le)
    positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with T hT hY
  let Y := Real.log (Real.log T)
  change 1 ≤ Y at hY
  have hY0 : 0 ≤ Y := by linarith
  have hfloor : (Nat.floor Y : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hcard : ((loglogPrimes T).card : ℝ) ≤ 2 * Y := by
    have hc : (loglogPrimes T).card ≤ Nat.floor Y + 1 := by
      change ((Finset.range (Nat.floor Y + 1)).filter Nat.Prime).card ≤ Nat.floor Y + 1
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    have hc' : ((loglogPrimes T).card : ℝ) ≤ (Nat.floor Y : ℝ) + 1 := by exact_mod_cast hc
    linarith
  have hs : (∑ p ∈ loglogPrimes T,
      (Real.log p / (Real.pi * Real.sqrt p)) * (1 + Real.log p)^2) ≤ 8*Y^4 := by
    calc
      _ ≤ ∑ _p ∈ loglogPrimes T, Y*(2*Y)^2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Nat.mem_primesBelow.mp hp
        have hn : p ≤ Nat.floor Y := Nat.lt_succ_iff.mp hp'.1
        have hpY : (p : ℝ) ≤ Y := (show (p : ℝ) ≤ (Nat.floor Y : ℝ) by exact_mod_cast hn).trans hfloor
        have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp'.2.one_le
        have hp0 : 0 < (p : ℝ) := by linarith
        have hl0 := Real.log_nonneg hp1
        have hlY := (Real.log_le_sub_one_of_pos hp0).trans (show (p : ℝ)-1 ≤ Y by linarith)
        have hsqrt : 1 ≤ Real.sqrt (p : ℝ) := by simpa using Real.sqrt_le_sqrt hp1
        have hden : 1 ≤ Real.pi * Real.sqrt (p : ℝ) :=
          one_le_mul_of_one_le_of_one_le (by linarith [Real.pi_gt_three]) hsqrt
        apply mul_le_mul ((div_le_self hl0 hden).trans hlY)
          (pow_le_pow_left₀ (by linarith) (by linarith : 1 + Real.log p ≤ 2*Y) 2)
          (sq_nonneg _) (by linarith)
      _ = ((loglogPrimes T).card : ℝ) * (Y*(2*Y)^2) := by simp
      _ ≤ 2*Y*(Y*(2*Y)^2) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hrate : 0 ≤ horizontalLogRate T := div_nonneg (sq_nonneg _) (Real.log_pos hT).le
  apply (mul_le_mul_of_nonneg_left hs hrate).trans_eq
  change (Y^2/Real.log T)*(8*Y^4) = 8*(Y^6/Real.log T)
  ring

end RiemannResearch.Analysis.MicroscopicSelbergPrimeTrace
