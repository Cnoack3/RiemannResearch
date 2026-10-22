import RiemannResearch.Analysis.FourierL1L2Plancherel
import RiemannResearch.RH.ArithmeticMellinPositiveHalfPlane
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.LinearCombination

/-!
# Arithmetic Mellin-Plancherel identity

The logarithmic lift of each bounded arithmetic error lies in L1 ∩ L2.
A change of variables identifies its Fourier integral with the Mellin integral;
ordinary-integral Plancherel then gives the complete spectral error identity
with angular-frequency normalization 1/(2π).
-/

open MeasureTheory FourierTransform Set
open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto

private def logarithmicHalfStepRaw (f : ℕ → ℝ) (t : ℝ) : ℂ :=
  (f ⌊Real.exp t⌋₊ : ℂ) * (Real.exp (-t / 2) : ℂ)

private def logarithmicHalfStep (f : ℕ → ℝ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator (logarithmicHalfStepRaw f)

private theorem logarithmicHalfStepRaw_measurable (f : ℕ → ℝ) :
    Measurable (logarithmicHalfStepRaw f) := by
  exact (Complex.continuous_ofReal.measurable.comp
    ((measurable_of_countable f).comp (Nat.measurable_floor.comp Real.measurable_exp))).mul
    (Complex.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_id.neg.div_const 2)))

private theorem logarithmicHalfStepRaw_norm_sq (f : ℕ → ℝ) (t : ℝ) :
    ‖logarithmicHalfStepRaw f t‖^2 = f ⌊Real.exp t⌋₊ ^ 2 * Real.exp (-t) := by
  have he : Real.exp (-t / 2)^2 = Real.exp (-t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [logarithmicHalfStepRaw, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, he]

private theorem logarithmicHalfStep_integrable {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) : Integrable (logarithmicHalfStep f) := by
  apply (integrable_indicator_iff measurableSet_Ioi).2
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-t / 2)) (Ioi 0) := by
    convert! integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0 using 1
    congr 1
    funext t
    congr 1
    ring
  apply (hi.const_mul C).mono' (logarithmicHalfStepRaw_measurable f).aestronglyMeasurable
  filter_upwards [] with t
  simp only [logarithmicHalfStepRaw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hf _) (Real.exp_nonneg _)

private theorem logarithmicHalfStep_memLp {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) : MemLp (logarithmicHalfStep f) 2 := by
  apply (memLp_indicator_iff_restrict measurableSet_Ioi).2
  apply (memLp_two_iff_integrable_sq_norm
    (logarithmicHalfStepRaw_measurable f).aestronglyMeasurable).2
  simp_rw [logarithmicHalfStepRaw_norm_sq]
  have hm : Measurable (fun t : ℝ => f ⌊Real.exp t⌋₊ ^ 2 * Real.exp (-t)) :=
    (((measurable_of_countable f).comp
      (Nat.measurable_floor.comp Real.measurable_exp)).pow_const 2).mul
      (Real.measurable_exp.comp measurable_id.neg)
  apply ((integrableOn_exp_neg_Ioi 0).const_mul (C^2)).mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
    abs_of_pos (Real.exp_pos _)]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf 0)
  have hs : f ⌊Real.exp t⌋₊ ^ 2 ≤ C^2 := by
    nlinarith [hf ⌊Real.exp t⌋₊, sq_abs (f ⌊Real.exp t⌋₊),
      abs_nonneg (f ⌊Real.exp t⌋₊)]
  exact mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _)

private theorem logarithmicHalfStep_energy (f : ℕ → ℝ)
    (hf : Summable (fun k => positiveWeight k * f k^2)) :
    (∫ t, ‖logarithmicHalfStep f t‖^2) = ∑' k, positiveWeight k * f k^2 := by
  have he : (fun t => ‖logarithmicHalfStep f t‖^2) =
      (Ioi (0 : ℝ)).indicator
        (fun t => f ⌊Real.exp t⌋₊ ^ 2 * Real.exp (-t)) := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [logarithmicHalfStep, indicator_of_mem ht,
        logarithmicHalfStepRaw_norm_sq]
    · simp [logarithmicHalfStep, ht]
  rw [he, integral_indicator measurableSet_Ioi]
  have h := integral_comp_exp_Ioi (fun x : ℝ => f ⌊x⌋₊^2 / x^2) 0
  have hfun : (fun t : ℝ => Real.exp t • (f ⌊Real.exp t⌋₊^2 / Real.exp t^2)) =
      fun t => f ⌊Real.exp t⌋₊^2 * Real.exp (-t) := by
    funext t
    simp only [smul_eq_mul, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [hfun, Real.exp_zero] at h
  exact h.trans (paretoStep_energy_identity f hf)

private def mellinCriticalPoint (w : ℝ) : ℂ :=
  (1 / 2 : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I

private theorem logarithmicHalfStep_factor (t w : ℝ) :
    (Real.exp t : ℂ) * (Real.exp t : ℂ)^(-mellinCriticalPoint w - 1) =
      Complex.exp (((-2 * Real.pi * t * w : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-t / 2) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)),
    ← Complex.ofReal_log (Real.exp_nonneg t), Real.log_exp,
    Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold mellinCriticalPoint
  push_cast
  ring

private theorem logarithmicHalfStep_fourier (f : ℕ → ℝ) (w : ℝ) :
    𝓕 (logarithmicHalfStep f) w =
      ∫ x in Ioi (1 : ℝ), (f ⌊x⌋₊ : ℂ) *
        (x : ℂ)^(-mellinCriticalPoint w - 1) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        Complex.exp (((-2 * Real.pi * t * w : ℝ) : ℂ) * Complex.I) •
          logarithmicHalfStep f t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      simp [logarithmicHalfStep, ht]
    _ = ∫ t in Ioi (0 : ℝ), Real.exp t •
        ((f ⌊Real.exp t⌋₊ : ℂ) *
          (Real.exp t : ℂ)^(-mellinCriticalPoint w - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [logarithmicHalfStep, indicator_of_mem ht, logarithmicHalfStepRaw,
        smul_eq_mul, Complex.real_smul]
      have h := logarithmicHalfStep_factor t w
      linear_combination -(f ⌊Real.exp t⌋₊ : ℂ) * h
    _ = _ := by
      simpa only [Real.exp_zero] using
        integral_comp_exp_Ioi
          (fun x : ℝ => (f ⌊x⌋₊ : ℂ) * (x : ℂ)^(-mellinCriticalPoint w - 1)) 0

private theorem arithmeticCombination_bounded_plancherel (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) :
    ∃ C : ℝ, ∀ k, |arithmeticCombination c k| ≤ C := by
  refine ⟨∑ p ∈ c.support, |c p| * ((p.2 : ℝ) * (p.1 : ℝ)), ?_⟩
  intro k
  unfold arithmeticCombination
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro p hp
  have ha : 0 < p.1 := by
    rcases (hc p hp).1 with h | h <;> omega
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (dilation_abs_le (fun j => residue_abs_le p.1 j ha) p.2 k) (abs_nonneg _)

private theorem arithmeticError_mellin_critical (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) (w : ℝ) :
    (∫ x in Ioi (1 : ℝ), (1 - arithmeticStep c x) *
      (x : ℂ)^(-mellinCriticalPoint w - 1)) =
      (1 - riemannZeta (mellinCriticalPoint w) *
        arithmeticMellinSymbol c (mellinCriticalPoint w)) / mellinCriticalPoint w := by
  have hs : (mellinCriticalPoint w).re = 1 / 2 := by simp [mellinCriticalPoint]
  obtain ⟨hstep, hI⟩ := arithmeticMellinIdentityTarget_proved c hc
    (mellinCriticalPoint w) (by rw [hs]; norm_num) (by rw [hs]; norm_num)
  have hp : (-mellinCriticalPoint w - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, hs]
    norm_num
  have hpow := integrableOn_Ioi_cpow_of_lt hp (by norm_num : (0 : ℝ) < 1)
  have he : (fun x : ℝ => (1 - arithmeticStep c x) *
      (x : ℂ)^(-mellinCriticalPoint w - 1)) = fun x : ℝ =>
      (x : ℂ)^(-mellinCriticalPoint w - 1) -
        arithmeticStep c x * (x : ℂ)^(-mellinCriticalPoint w - 1) := by
    funext x
    ring
  rw [he, integral_sub hpow hstep, hI,
    integral_Ioi_cpow_of_lt hp (by norm_num : (0 : ℝ) < 1)]
  simp <;> ring

/-- The full Mellin-Plancherel target, with the actual continuous spectral
integral and the exact angular-frequency normalization. -/
theorem arithmeticPlancherelTarget_proved : ArithmeticPlancherelTarget := by
  intro c hc
  obtain ⟨C, hC⟩ := arithmeticCombination_bounded_plancherel c hc
  let f : ℕ → ℝ := fun k => 1 - arithmeticCombination c k
  have hf : ∀ k, |f k| ≤ 1 + C := by
    intro k
    calc
      _ ≤ |(1 : ℝ)| + |arithmeticCombination c k| := by
        simpa only [f, sub_zero, zero_sub, abs_neg] using
          abs_sub_le (1 : ℝ) 0 (arithmeticCombination c k)
      _ ≤ _ := by simpa using add_le_add (le_refl (1 : ℝ)) (hC k)
  have hfs : Summable (fun k => positiveWeight k * f k^2) :=
    weighted_summable_of_bounded (error_square_bounded hC)
  have hPl := RiemannResearch.Analysis.integral_norm_sq_fourier_of_integrable
    (logarithmicHalfStep_integrable hf) (logarithmicHalfStep_memLp hf)
  have hE : (∫ t, ‖logarithmicHalfStep f t‖^2) = arithmeticFullError c :=
    logarithmicHalfStep_energy f hfs
  rw [hE] at hPl
  let G : ℝ → ℝ := fun t =>
    ‖1 - riemannZeta ((1/2 : ℂ) + t * Complex.I) *
      arithmeticMellinSymbol c ((1/2 : ℂ) + t * Complex.I)‖^2 / ((1/4 : ℝ) + t^2)
  have hFourier (w : ℝ) : ‖𝓕 (logarithmicHalfStep f) w‖^2 = G (2 * Real.pi * w) := by
    rw [logarithmicHalfStep_fourier]
    have he : (∫ x in Ioi (1 : ℝ), (f ⌊x⌋₊ : ℂ) *
        (x : ℂ)^(-mellinCriticalPoint w - 1)) =
        (1 - riemannZeta (mellinCriticalPoint w) *
          arithmeticMellinSymbol c (mellinCriticalPoint w)) / mellinCriticalPoint w := by
      simpa only [f, Complex.ofReal_sub, Complex.ofReal_one, arithmeticStep] using
        arithmeticError_mellin_critical c hc w
    rw [he, norm_div, div_pow]
    have hnorm : ‖mellinCriticalPoint w‖^2 = (1 / 4 : ℝ) + (2 * Real.pi * w)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [mellinCriticalPoint] <;> ring
    rw [hnorm]
    rfl
  simp_rw [hFourier] at hPl
  have hscale := Measure.integral_comp_mul_left G (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [abs_of_pos (inv_pos.mpr hpi), smul_eq_mul] at hscale
  change arithmeticFullError c = (1 / (2 * Real.pi)) * ∫ t, G t
  rw [← hPl, hscale]
  simp only [one_div]

end RiemannResearch.RH.Pareto
