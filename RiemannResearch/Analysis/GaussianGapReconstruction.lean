import RiemannResearch.Analysis.GaussianOrdinateSimplicity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-sided Gaussian criterion on the signed Landau reconstruction

The Fourier weight has mass one. Subtracting the occurrence diagonal leaves
a uniform error of at most three divided by height for every positive precision.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Zeta23
open scoped Topology ENNReal NNReal
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Cycles-per-unit Fourier weight of the physical test exp(-a x²). -/
def gaussianFrequencyWeight (a h : ℝ) : ℝ :=
  Real.sqrt (Real.pi / a) * Real.exp (-(Real.pi ^ 2 / a) * h ^ 2)

private theorem gaussianFrequencyWeight_eq_pdf {a : ℝ} (ha : 0 < a) :
    gaussianFrequencyWeight a = gaussianPDFReal 0
      ⟨a / (2 * Real.pi ^ 2), by positivity⟩ := by
  funext y
  change Real.sqrt (Real.pi / a) * Real.exp (-(Real.pi ^ 2 / a) * y ^ 2) =
    (Real.sqrt (2 * Real.pi * (a / (2 * Real.pi ^ 2))))⁻¹ *
      Real.exp (-(y - 0) ^ 2 / (2 * (a / (2 * Real.pi ^ 2))))
  have he : 2 * Real.pi * (a / (2 * Real.pi ^ 2)) = a / Real.pi := by
    field_simp
  rw [sub_zero, he, ← Real.sqrt_inv, inv_div]
  congr 2
  field_simp

/-- The cosine transform, integrability and mass are all for the very same weight. -/
theorem gaussianFrequencyWeight_spec {a : ℝ} (ha : 0 < a) :
    Integrable (gaussianFrequencyWeight a) ∧
    (∫ h : ℝ, |gaussianFrequencyWeight a h|) = 1 ∧
    ∀ x : ℝ, cosineGapProbe (gaussianFrequencyWeight a) x = Real.exp (-a * x ^ 2) := by
  let v : ℝ≥0 := ⟨a / (2 * Real.pi ^ 2), by positivity⟩
  have hv : v ≠ 0 := by
    apply ne_of_gt
    change 0 < a / (2 * Real.pi ^ 2)
    positivity
  rw [gaussianFrequencyWeight_eq_pdf ha]
  change Integrable (gaussianPDFReal 0 v) ∧ _ ∧ _
  refine ⟨integrable_gaussianPDFReal _ _, ?_, ?_⟩
  · change (∫ h : ℝ, |gaussianPDFReal 0 v h|) = 1
    calc
      _ = ∫ h : ℝ, gaussianPDFReal 0 v h := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => abs_of_nonneg (gaussianPDFReal_nonneg 0 v y)
      _ = 1 := integral_gaussianPDFReal_eq_one 0 hv
  · intro x
    let t := 2 * Real.pi * x
    let F (y : ℝ) := Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
    have hi : Integrable F (gaussianReal 0 v) := by
      apply (integrable_const (1 : ℝ)).mono' (by dsimp [F]; fun_prop)
      exact ae_of_all _ fun y => by simp [F, Complex.norm_exp]
    have hchar : (charFun (gaussianReal 0 v) t).re = Real.exp (-(v : ℝ) * t ^ 2 / 2) := by
      rw [charFun_gaussianReal]
      simp [Complex.exp_re, ← Complex.ofReal_pow, neg_div]
    calc
      cosineGapProbe (gaussianPDFReal 0 v) x =
          ∫ y : ℝ, Real.cos (t * y) ∂(gaussianReal 0 v) := by
        rw [integral_gaussianReal_eq_integral_smul hv]
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          simp only [smul_eq_mul, t, mul_comm (gaussianPDFReal 0 v y)]
          congr 2
          ring
      _ = (charFun (gaussianReal 0 v) t).re := by
        rw [charFun_apply_real]
        change _ = RCLike.re (∫ y, F y ∂(gaussianReal 0 v))
        rw [← integral_re hi]
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          change Real.cos (t * y) = (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)).re
          simp [Complex.exp_re]
      _ = Real.exp (-a * x ^ 2) := by
        rw [hchar]
        congr 1
        change -(a / (2 * Real.pi ^ 2)) * (2 * Real.pi * x) ^ 2 / 2 = -a * x ^ 2
        field_simp

/-- Upper bound on the Fourier mass inside any fixed symmetric band. -/
theorem gaussianFrequencyWeight_band_mass_le {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) :
    (∫ h in -B..B, gaussianFrequencyWeight a h) ≤ 2 * B * Real.sqrt (Real.pi / a) := by
  have hcont : Continuous (gaussianFrequencyWeight a) := by
    unfold gaussianFrequencyWeight
    fun_prop
  have hb : -B ≤ B := by linarith
  calc
    _ ≤ ∫ _h in -B..B, Real.sqrt (Real.pi / a) := by
      apply intervalIntegral.integral_mono_on hb
        (hcont.intervalIntegrable ..) intervalIntegrable_const
      intro y _
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.exp_le_one_iff.mpr (by
        have : 0 ≤ Real.pi ^ 2 / a := by positivity
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr this) (sq_nonneg y)))
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- The integrated signed Landau reconstruction, with its occurrence diagonal retained. -/
def reconstructedGaussianPower (a T : ℝ) : ℝ :=
  ∫ h : ℝ, reconstructedGapSpectrum T (2 * Real.pi * h * (Real.log T / (2 * Real.pi)))
    (Real.log T) * gaussianFrequencyWeight a h

/-- The same error bound works for every positive Gaussian precision. -/
theorem gaussianFactorialMoment_reconstruction {T a : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T)
    (ha : 0 < a) :
    |gaussianFactorialMoment a T - (reconstructedGaussianPower a T - 1)| ≤ 3 / T := by
  obtain ⟨hi, hm, hw⟩ := gaussianFrequencyWeight_spec ha
  have h := reconstructed_factorial_cosine_gap_test T (Real.log T / (2 * Real.pi))
    (Real.log T) (Real.log_pos hT).le hN hi
  rw [factorialCosineGapTest] at h
  simp_rw [hw] at h
  rw [hm, Real.exp_neg, Real.exp_log (zero_lt_one.trans hT)] at h
  simpa [gaussianFactorialMoment_eq_sum, reconstructedGaussianPower, div_eq_mul_inv] using h

private theorem eventually_gaussian_reconstruction_close {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      |gaussianFactorialMoment a T - (reconstructedGaussianPower a T - 1)| < ε := by
  filter_upwards [eventually_gt_atTop (max 1 (3 / ε)), eventually_count_pos] with T hT hN
  have hT1 := (le_max_left _ _).trans_lt hT
  have hdiv := (le_max_right _ _).trans_lt hT
  apply (gaussianFactorialMoment_reconstruction hT1 hN ha).trans_lt
  apply (div_lt_iff₀ (zero_lt_one.trans hT1)).2
  linarith only [(div_lt_iff₀ hε).1 hdiv]

/-- Only a cofinal family of eventual one-sided upper bounds for reconstructed
powers suffices, including when individual height limits fail to exist. -/
theorem gaussian_liminf_eq_zero_iff_reconstructed_upper :
    liminf gaussianHeightLimsup atTop = 0 ↔
    ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, ∃ n ≥ max 1 k,
      ∀ᶠ T : ℝ in atTop, reconstructedGaussianPower n T < 1 + ε := by
  rw [gaussian_liminf_limsup_eq_zero_iff]
  constructor
  · intro h ε hε k
    have he : 0 < ε / 2 := half_pos hε
    obtain ⟨n, hn, hphys⟩ := h (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr he) (max 1 k)
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 k).trans hn))
    refine ⟨n, hn, ?_⟩
    filter_upwards [hphys, eventually_gaussian_reconstruction_close hnpos he] with T hT herr
    linarith only [(ENNReal.ofReal_lt_ofReal_iff he).1 hT, (abs_lt.mp herr).1]
  · intro h ε hε k
    by_cases ht : ε = ⊤
    · exact ⟨k, le_rfl, Eventually.of_forall fun T => ht ▸ ENNReal.ofReal_lt_top⟩
    have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' ht
    obtain ⟨n, hn, hpow⟩ := h (ε.toReal / 2) (half_pos he) k
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 k).trans hn))
    refine ⟨n, (le_max_right 1 k).trans hn, ?_⟩
    filter_upwards [hpow, eventually_gaussian_reconstruction_close hnpos (half_pos he)]
      with T hT herr
    rw [← ENNReal.ofReal_toReal ht]
    apply (ENNReal.ofReal_lt_ofReal_iff he).2
    linarith only [hT, (abs_lt.mp herr).2]

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.gaussian_liminf_eq_zero_iff_reconstructed_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gaussian_liminf_eq_zero_iff_reconstructed_upper

end RiemannResearch.Analysis.ActualZeroOrdinate
