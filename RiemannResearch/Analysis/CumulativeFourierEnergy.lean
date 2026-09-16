import RiemannResearch.Analysis.CumulativeTailKernel
import RiemannResearch.Analysis.FourierL1L2Plancherel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Continuous Fourier representation of the complete cumulative-charge energy

This is an ordinary L1/L2 Plancherel proof for finite complex charges.
No zero sampling, RH, analytic number theory, or discrete replacement of the
continuous spectral integral is used. Angular frequency is normalized explicitly.
Thus the Fourier and max-kernel formulas describe the same full signed energy.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform

namespace RiemannResearch.Analysis.CumulativeFourierEnergy
open CumulativeTailKernel

def expTail (a b : ℝ) : ℝ → ℂ :=
  (Ioi b).indicator (fun t => (Real.exp (-a * t) : ℂ))

lemma expTail_integrable (a b : ℝ) (ha : 0 < a) : Integrable (expTail a b) := by
  rw [expTail, integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) b).ofReal

lemma expTail_norm_sq (a b t : ℝ) :
    ‖expTail a b t‖ ^ 2 = (Ioi b).indicator (fun t => Real.exp ((-2 * a) * t)) t := by
  by_cases ht : b < t
  · simp only [expTail, indicator_apply, mem_Ioi, if_pos ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), pow_two]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp [expTail, indicator_apply, mem_Ioi, ht]

lemma expTail_memLp (a b : ℝ) (ha : 0 < a) : MemLp (expTail a b) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (expTail_integrable a b ha).aestronglyMeasurable).mpr
  simp_rw [expTail_norm_sq]
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_exp_mul_Ioi (by linarith : -2 * a < 0) b

def point (a w : ℝ) : ℂ := (a : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I

@[simp] lemma point_re (a w : ℝ) : (point a w).re = a := by simp [point]

lemma oscillated_tail (a b w t : ℝ) :
    Complex.exp (((-2 * Real.pi * t * w : ℝ) : ℂ) * Complex.I) * expTail a b t =
      (Ioi b).indicator (fun t => Complex.exp (-point a w * (t : ℂ))) t := by
  by_cases ht : b < t
  · simp only [expTail, indicator_apply, mem_Ioi, if_pos ht, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    unfold point
    push_cast
    ring
  · simp [expTail, indicator_apply, mem_Ioi, ht]

lemma oscillated_tail_integrable (a b w : ℝ) (ha : 0 < a) :
    Integrable (fun t => Complex.exp (((-2 * Real.pi * t * w : ℝ) : ℂ) * Complex.I) *
      expTail a b t) := by
  simp_rw [oscillated_tail]
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_exp_mul_complex_Ioi (by simp; linarith) b

lemma integral_oscillated_tail (a b w : ℝ) (ha : 0 < a) :
    (∫ t : ℝ, Complex.exp (((-2 * Real.pi * t * w : ℝ) : ℂ) * Complex.I) *
      expTail a b t) = Complex.exp (-point a w * (b : ℂ)) / point a w := by
  simp_rw [oscillated_tail]
  rw [integral_indicator measurableSet_Ioi,
    integral_exp_mul_complex_Ioi (by simp; linarith) b]
  simp only [neg_div_neg_eq]

variable {ι : Type*}

def timeSum (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a t : ℝ) : ℂ :=
  ∑ i ∈ S, c i * expTail a (Real.log (q i)) t

lemma timeSum_integrable (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a : ℝ) (ha : 0 < a) :
    Integrable (timeSum S q c a) :=
  integrable_finsetSum S (fun i _ => (expTail_integrable a (Real.log (q i)) ha).const_mul (c i))

lemma timeSum_memLp (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a : ℝ) (ha : 0 < a) :
    MemLp (timeSum S q c a) 2 :=
  memLp_finsetSum S (fun i _ => (expTail_memLp a (Real.log (q i)) ha).const_mul (c i))

lemma timeSum_factor (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a t : ℝ)
    (hq : ∀ i ∈ S, 0 < q i) :
    timeSum S q c a t = (Real.exp (-a * t) : ℂ) * cumulative S q c (Real.exp t) := by
  unfold timeSum cumulative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [expTail, indicator_apply, mem_Ioi, Real.log_lt_iff_lt_exp (hq i hi)]
  split_ifs <;> ring

lemma exponential_energy_factor (a t : ℝ) :
    Real.exp (-a * t) ^ 2 = Real.exp t * (Real.exp t) ^ (-2 * a - 1) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, pow_two,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma timeSum_energy_factor (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a t : ℝ)
    (hq : ∀ i ∈ S, 0 < q i) :
    ‖timeSum S q c a t‖ ^ 2 = Real.exp t *
      (‖cumulative S q c (Real.exp t)‖ ^ 2 * (Real.exp t) ^ (-2 * a - 1)) := by
  rw [timeSum_factor S q c a t hq, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), exponential_energy_factor]
  ring

lemma timeSum_zero_nonpos (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a t : ℝ)
    (hq : ∀ i ∈ S, 1 ≤ q i) (ht : t ≤ 0) : timeSum S q c a t = 0 := by
  rw [timeSum_factor S q c a t (fun i hi => lt_of_lt_of_le zero_lt_one (hq i hi)),
    cumulative_zero_below S q c 1 (Real.exp t) hq (Real.exp_le_one_iff.mpr ht), mul_zero]

lemma timeSum_energy (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a : ℝ)
    (hq : ∀ i ∈ S, 1 ≤ q i) :
    (∫ t : ℝ, ‖timeSum S q c a t‖ ^ 2) =
      ∫ x : ℝ in Ioi 1, ‖cumulative S q c x‖ ^ 2 * x ^ (-2 * a - 1) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, ‖timeSum S q c a t‖ ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      rw [timeSum_zero_nonpos S q c a t hq (le_of_not_gt ht)]
      simp
    _ = _ := by
      simp_rw [timeSum_energy_factor S q c a _ (fun i hi => lt_of_lt_of_le zero_lt_one (hq i hi))]
      simpa only [smul_eq_mul, Real.exp_zero] using
        integral_comp_exp_Ioi (fun x : ℝ => ‖cumulative S q c x‖ ^ 2 * x ^ (-2 * a - 1)) 0

lemma timeSum_fourier (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a w : ℝ) (ha : 0 < a) :
    𝓕 (timeSum S q c a) w =
      (∑ i ∈ S, c i * Complex.exp (-point a w * (Real.log (q i) : ℂ))) / point a w := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have he (t : ℝ) :
      Complex.exp (((-2 * Real.pi * t * w : ℝ) : ℂ) * Complex.I) * timeSum S q c a t =
      ∑ i ∈ S, c i * (Complex.exp (((-2 * Real.pi * t * w : ℝ) : ℂ) * Complex.I) *
        expTail a (Real.log (q i)) t) := by
    unfold timeSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [he]
  rw [integral_finsetSum S (fun i _ =>
    (oscillated_tail_integrable a (Real.log (q i)) w ha).const_mul (c i))]
  simp_rw [integral_const_mul, integral_oscillated_tail a _ w ha, ← mul_div_assoc]
  exact (Finset.sum_div _ _ _).symm

def numerator (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a u : ℝ) : ℂ :=
  ∑ i ∈ S, c i * (q i : ℂ) ^ (-(a : ℂ) - (u : ℂ) * Complex.I)

lemma exp_log_eq_cpow (a u q : ℝ) (hq : 0 < q) :
    Complex.exp (-((a : ℂ) + (u : ℂ) * Complex.I) * (Real.log q : ℂ)) =
      (q : ℂ) ^ (-(a : ℂ) - (u : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
    ← Complex.ofReal_log hq.le]
  congr 1
  ring

lemma timeSum_fourier_norm (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (a w : ℝ)
    (ha : 0 < a) (hq : ∀ i ∈ S, 0 < q i) :
    ‖𝓕 (timeSum S q c a) w‖ ^ 2 =
      ‖numerator S q c a (2 * Real.pi * w)‖ ^ 2 / (a ^ 2 + (2 * Real.pi * w) ^ 2) := by
  rw [timeSum_fourier S q c a w ha, norm_div, div_pow]
  have hn : (∑ i ∈ S, c i * Complex.exp (-point a w * (Real.log (q i) : ℂ))) =
      numerator S q c a (2 * Real.pi * w) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [point, exp_log_eq_cpow a _ _ (hq i hi)]
  rw [hn]
  congr 1
  simp [point, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Plancherel in the actual weighted cumulative norm, with angular frequency. -/
theorem cumulative_fourier_energy_half (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (a : ℝ) (ha : 0 < a) (hq : ∀ i ∈ S, 1 ≤ q i) :
    (∫ x : ℝ in Ioi 1, ‖cumulative S q c x‖ ^ 2 * x ^ (-2 * a - 1)) =
      (1 / (2 * Real.pi)) * ∫ u : ℝ, ‖numerator S q c a u‖ ^ 2 / (a ^ 2 + u ^ 2) := by
  have hp := RiemannResearch.Analysis.integral_norm_sq_fourier_of_integrable
    (timeSum_integrable S q c a ha) (timeSum_memLp S q c a ha)
  rw [timeSum_energy S q c a hq] at hp
  simp_rw [timeSum_fourier_norm S q c a _ ha
    (fun i hi => lt_of_lt_of_le zero_lt_one (hq i hi))] at hp
  have hscale := Measure.integral_comp_mul_left
    (fun u : ℝ => ‖numerator S q c a u‖ ^ 2 / (a ^ 2 + u ^ 2)) (2 * Real.pi)
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)), smul_eq_mul] at hscale
  rw [hscale] at hp
  simpa only [one_div] using hp.symm

/-- The complete signed charge energy has a Cauchy-weighted continuous Fourier
representation. This is not a discrete zero-sampling identity. -/
theorem cumulativeLE_fourier_energy (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (s : ℝ) (hs : 0 < s) (hq : ∀ i ∈ S, 1 ≤ q i) :
    (∫ x : ℝ in Ioi 1, ‖cumulativeLE S q c x‖ ^ 2 * x ^ (-s - 1)) =
      (1 / (2 * Real.pi)) * ∫ u : ℝ,
        ‖numerator S q c (s / 2) u‖ ^ 2 / ((s / 2) ^ 2 + u ^ 2) := by
  have h := cumulative_fourier_energy_half S q c (s / 2) (by positivity) hq
  have hexp : -2 * (s / 2) - 1 = -s - 1 := by ring
  rw [hexp] at h
  rw [cumulativeLE_energy S q c s hs hq,
    ← cumulative_energy_Ioi_one S q c s hs hq]
  exact h

end RiemannResearch.Analysis.CumulativeFourierEnergy
