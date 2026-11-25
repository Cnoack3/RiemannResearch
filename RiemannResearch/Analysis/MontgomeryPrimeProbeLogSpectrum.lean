import RiemannResearch.Analysis.MontgomeryPrimeProbeCenteredPlancherel
import RiemannResearch.Analysis.DirichletMeanSquare

/-! # The prime probe on the unscaled logarithmic line -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set ZeroOrdinate
open scoped Topology BigOperators

/-- The prime-power mass at the unscaled frequency `log n`. -/
def primeAtomWeight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / n

def primeLogPolynomial (L t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊, (primeAtomWeight n : ℂ) * phase (Real.log n) t

def logBoxProbe (L t : ℝ) : ℂ := ∫ y in (0:ℝ)..L, phase y t

def primeLogDiscrepancy (L t : ℝ) : ℂ := primeLogPolynomial L t - logBoxProbe L t

theorem logPolynomial_eq_scaled_probe {L : ℝ} (hL : 0 < L) (t : ℝ) :
    primeLogPolynomial L t = (L : ℂ) * primeFourierProbe (Real.exp L) (L*t/(2*Real.pi)) := by
  simp only [primeLogPolynomial, primeFourierProbe, Real.log_exp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have ht : 2*Real.pi*(L*t/(2*Real.pi)) = L*t := by field_simp
  rw [ht]
  simp only [primeAtomWeight, phase, Complex.ofReal_div, Complex.ofReal_mul]
  have hLC := Complex.ofReal_ne_zero.mpr hL.ne'
  rw [show (↑L * ↑t * Complex.I * (↑(Real.log n) / ↑L) : ℂ) =
    (↑(Real.log n) * ↑t) * Complex.I by field_simp]
  field_simp
  <;> ring

theorem logBoxProbe_eq_scaled_continuum {L : ℝ} (hL : 0 < L) (t : ℝ) :
    logBoxProbe L t = (L : ℂ) * primeContinuumProbe (L*t/(2*Real.pi)) := by
  have hs := intervalIntegral.integral_comp_mul_left (fun y => phase y t)
    (a := (0:ℝ)) (b := 1) hL.ne'
  rw [mul_zero, mul_one, Complex.real_smul] at hs
  have ht : 2*Real.pi*(L*t/(2*Real.pi)) = L*t := by field_simp
  have he : primeContinuumProbe (L*t/(2*Real.pi)) = ∫ v in (0:ℝ)..1, phase (L*v) t := by
    unfold primeContinuumProbe phase
    rw [ht]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [Complex.ofReal_mul]
    congr 1
    ring
  rw [he, hs, logBoxProbe, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne']

theorem primeLogDiscrepancy_eq_scaled {L : ℝ} (hL : 0 < L) (t : ℝ) :
    primeLogDiscrepancy L t = (L : ℂ) *
      (primeFourierProbe (Real.exp L) (L*t/(2*Real.pi)) -
        primeContinuumProbe (L*t/(2*Real.pi))) := by
  rw [primeLogDiscrepancy, logPolynomial_eq_scaled_probe hL, logBoxProbe_eq_scaled_continuum hL,
    mul_sub]

private def remainderPhase (t y : ℝ) : ℂ := (logMertensRemainder y : ℂ) * phase y t

/-- The unscaled Abel formula gives the center coefficient one at every frequency. -/
theorem primeLogDiscrepancy_abel {L : ℝ} (hL : 0 < L) (t : ℝ) :
    primeLogDiscrepancy L t = (mertensCenter : ℂ) +
      (logMertensRemainder L : ℂ) * phase L t -
      ((t : ℂ)*Complex.I) * ∫ y in (0:ℝ)..L, (logMertensRemainder y : ℂ) * phase y t := by
  let T := Real.exp L
  have hT : 1 < T := Real.one_lt_exp_iff.mpr hL
  have hc (v : ℝ) : primeLogCDF T v - v - mertensCenter/L = logMertensRemainder (L*v)/L := by
    rw [primeLogCDF_sub_eq_centered hT, show Real.log T = L from Real.log_exp _]
    ring
  rw [primeLogDiscrepancy_eq_scaled hL, primeFourierProbe_sub_eq_cdf_shift hT (mertensCenter/L)]
  dsimp only
  simp_rw [hc]
  rw [mul_one, show 2*Real.pi*(L*t/(2*Real.pi)) = L*t by field_simp]
  have hp (v : ℝ) : Complex.exp ((↑(L*t):ℂ)*Complex.I*↑v) = phase (L*v) t := by
    unfold phase
    push_cast
    congr 1
    ring
  simp_rw [hp, Complex.ofReal_div, div_mul_eq_mul_div]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_mul_left
    (fun y => (logMertensRemainder y : ℂ)*phase y t) (a := 0) (b := 1) hL.ne',
    mul_zero, mul_one, Complex.real_smul, Complex.ofReal_inv]
  simp only [phase, Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne']

private theorem remainderPhase_interval {Y L : ℝ} (hY : 0 ≤ Y) (hYL : Y ≤ L) (t : ℝ) :
    IntervalIntegrable (remainderPhase t) volume Y L := by
  have hi : IntervalIntegrable logMertensRemainder volume Y L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hYL).2
      (integrableOn_logMertensRemainder.mono_set (fun _ hy => hY.trans_lt hy.1))
  have hc : IntervalIntegrable (fun y => (logMertensRemainder y : ℂ)) volume Y L :=
    ⟨hi.1.ofReal, hi.2.ofReal⟩
  have hp : Continuous (fun y => phase y t) := by unfold phase; fun_prop
  exact hc.mul_continuousOn hp.continuousOn

/-- The truncation error is bounded by the endpoint and integral tails of the PNT remainder. -/
theorem primeLogDiscrepancy_truncation {Y L : ℝ} (hY : 0 < Y) (hYL : Y ≤ L) (t : ℝ) :
    ‖primeLogDiscrepancy L t - primeLogDiscrepancy Y t‖ ≤
      |logMertensRemainder L| + |logMertensRemainder Y| +
        |t| * ∫ y in Y..L, |logMertensRemainder y| := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (remainderPhase_interval (le_refl 0) hY.le t) (remainderPhase_interval hY.le hYL t)
  have he : primeLogDiscrepancy L t - primeLogDiscrepancy Y t =
      (logMertensRemainder L : ℂ)*phase L t - (logMertensRemainder Y : ℂ)*phase Y t -
      ((t : ℂ)*Complex.I) * ∫ y in Y..L, remainderPhase t y := by
    rw [primeLogDiscrepancy_abel (hY.trans_le hYL), primeLogDiscrepancy_abel hY]
    unfold remainderPhase at hsplit ⊢
    rw [← hsplit]
    ring
  rw [he]
  have hn := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := remainderPhase t) hYL
  simp only [remainderPhase, norm_mul, phase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs] at hn
  calc
    _ ≤ (‖(logMertensRemainder L : ℂ)*phase L t‖ + ‖(logMertensRemainder Y : ℂ)*phase Y t‖) +
          ‖((t : ℂ)*Complex.I) * ∫ y in Y..L, remainderPhase t y‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_mul, phase_norm, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hn (abs_nonneg _))

theorem primeLogDiscrepancy_quartic_truncation :
    ∃ K > (0:ℝ), ∀ {z L t : ℝ}, 1 ≤ z → z ≤ L → |t| ≤ z^4 →
      ‖primeLogDiscrepancy L t - primeLogDiscrepancy z t‖ ≤ K/z := by
  obtain ⟨C, hC, h⟩ := logMertensRemainder_fifth_tail
  refine ⟨3*C, by positivity, fun {z L t} hz hzL ht => ?_⟩
  have hz0 : 0 < z := by linarith
  obtain ⟨hp, hi⟩ := h hz hzL
  refine (primeLogDiscrepancy_truncation hz0 hzL t).trans ?_
  calc
    _ ≤ C/z^5 + C/z^5 + z^4*(C/z^5) :=
      add_le_add (add_le_add hp (h hz le_rfl).1) (mul_le_mul ht hi
        (intervalIntegral.integral_nonneg hzL (fun y _ => abs_nonneg _)) (by positivity))
    _ ≤ 3*C/z := by
      have hz4 : 1 ≤ z^4 := one_le_pow₀ hz
      field_simp [hz0.ne']
      nlinarith [mul_le_mul_of_nonneg_left hz4 hC.le]

end RiemannResearch.Analysis.MontgomeryPrimeTrace
