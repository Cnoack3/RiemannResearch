import RiemannResearch.Analysis.MontgomeryPrimeProbeSineKernel
import RiemannResearch.Analysis.MontgomeryPrimeProbeSincExpansion
import RiemannResearch.Analysis.MontgomerySampledCountError
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Positive prime-power pair contributions to the two-point determinant

The kernel coordinates are real Fourier test coordinates. Its feature indices
are the prime powers in the logarithmic von Mangoldt measure. We compute the
determinant and compare its integral to the actual ordinate counts.
Source: Compact Orbit M13 and the Mellin / prime-orbit handoff.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace RiemannResearch.Analysis.MontgomeryPrimeTrace

open MontgomeryFormFactor MontgomeryPositiveGap ZeroOrdinate

def probeDiagonalMass (T : ℝ) : ℝ := (primeFourierProbe T 0).re

theorem primeFourierProbe_zero_eq_mass (T : ℝ) :
    primeFourierProbe T 0 = (probeDiagonalMass T : ℂ) := by
  unfold probeDiagonalMass primeFourierProbe
  simp

private theorem probe_neg (T u : ℝ) :
    primeFourierProbe T (-u) = conj (primeFourierProbe T u) := by
  unfold primeFourierProbe
  simp only [map_sum, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat, map_ofNat]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 2
  push_cast
  ring

/-- Real value of the unnormalized two-point determinant at separation u. -/
def primePairDeterminant (T u : ℝ) : ℝ :=
  probeDiagonalMass T ^ 2 - ‖primeFourierProbe T u‖ ^ 2

theorem det_primeProbeKernel_pair (T x y : ℝ) :
    Matrix.det !![primeProbeKernel T x x, primeProbeKernel T x y;
      primeProbeKernel T y x, primeProbeKernel T y y] =
      (primePairDeterminant T (x-y) : ℂ) := by
  rw [Matrix.det_fin_two]
  change primeFourierProbe T (x-x) * primeFourierProbe T (y-y) -
      primeFourierProbe T (x-y) * primeFourierProbe T (y-x) = _
  simp only [sub_self, primeFourierProbe_zero_eq_mass]
  rw [show y-x = -(x-y) by ring, probe_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [primePairDeterminant, pow_two]

private theorem squaredProbe_cosine {κ : Type*} [Fintype κ] (f w : κ → ℝ) (u : ℝ) :
    ‖probeKernel f w u‖^2 = ∑ i, ∑ j, (w i*w j)*Real.cos (u*(f i-f j)) := by
  have hp (v : ℝ) : (phase v u).re = Real.cos (u*v) := by
    calc
      (phase v u).re = Real.cos (v*u) := Complex.exp_ofReal_mul_I_re _
      _ = _ := by rw [mul_comm]
  have h := congrArg Complex.re (probe_energy_expansion f w u)
  rw [Complex.ofReal_re] at h
  simpa [Complex.mul_re, hp] using h

/-- Each ordered prime-power pair contributes its weight times one minus its
relative phase cosine. Equal log frequencies contribute zero. -/
theorem primePairDeterminant_eq_sum (T u : ℝ) :
    let s := Finset.Ioc 0 ⌊T⌋₊
    let w (n : ℕ) := ArithmeticFunction.vonMangoldt n / (n : ℝ) / Real.log T
    let f (n : ℕ) := 2 * Real.pi * Real.log n / Real.log T
    primePairDeterminant T u =
      ∑ n ∈ s, ∑ m ∈ s, w n * w m * (1 - Real.cos (u * (f n - f m))) := by
  classical
  intro s w f
  have hprobe (v : ℝ) : primeFourierProbe T v =
      probeKernel (fun n : s => f n) (fun n : s => w n) v := by
    rw [probeKernel, Finset.sum_coe_sort s (fun n : ℕ => (w n : ℂ)*phase (f n) v)]
    unfold primeFourierProbe
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    unfold phase
    congr 1
    dsimp [f]
    push_cast
    ring
  have he (v : ℝ) : ‖primeFourierProbe T v‖^2 =
      ∑ n ∈ s, ∑ m ∈ s, (w n*w m)*Real.cos (v*(f n-f m)) := by
    rw [hprobe, squaredProbe_cosine]
    let term (i j : ℕ) := w i * w j * Real.cos (v * (f i - f j))
    calc
      (∑ i : s, ∑ j : s, term i j) = ∑ i : s, ∑ j ∈ s, term i j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_coe_sort s (fun j : ℕ => term i j))
      _ = _ := Finset.sum_coe_sort s (fun i : ℕ => ∑ j ∈ s, term i j)
  have hm : probeDiagonalMass T ^ 2 = ‖primeFourierProbe T 0‖^2 := by
    rw [primeFourierProbe_zero_eq_mass, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [primePairDeterminant, hm, he, he]
  simp only [zero_mul, Real.cos_zero, mul_one]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]

theorem primePairDeterminant_nonneg {T : ℝ} (hT : 1 < T) (u : ℝ) :
    0 ≤ primePairDeterminant T u := by
  rw [primePairDeterminant_eq_sum]
  apply Finset.sum_nonneg
  intro n _
  apply Finset.sum_nonneg
  intro m _
  have hn (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k / (k : ℝ) / Real.log T :=
    div_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
      (Real.log_pos hT).le
  exact mul_nonneg (mul_nonneg (hn _) (hn _)) (sub_nonneg.mpr (Real.cos_le_one _))

theorem probeDiagonalMass_tendsto_one :
    Tendsto probeDiagonalMass atTop (𝓝 1) := by
  have ht : Tendsto (fun T => primeFourierProbe T 0) atTop (𝓝 (1 : ℂ)) := by
    simpa [primeProbeKernel] using primeProbeKernel_tendsto 0 0
  exact (Complex.continuous_re.tendsto _).comp ht

/-- Centering the frequency interval and calibrating its total mass gives a
unit-intensity sine kernel at each pair of fixed test coordinates. -/
theorem normalized_centeredPrimeProbeKernel_tendsto (x y : ℝ) :
    Tendsto (fun T => centeredPrimeProbeKernel T x y / (probeDiagonalMass T : ℂ)) atTop
      (𝓝 (Real.sinc (Real.pi * (x-y)) : ℂ)) := by
  have hm : Tendsto (fun T => (probeDiagonalMass T : ℂ)) atTop (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp probeDiagonalMass_tendsto_one
  have ht := (centeredPrimeProbeKernel_tendsto x y).div hm one_ne_zero
  change Tendsto (fun T => centeredPrimeProbeKernel T x y / (probeDiagonalMass T : ℂ))
    atTop (𝓝 ((Real.sinc (Real.pi * (x-y)) : ℂ) / 1)) at ht
  simpa only [div_one] using ht

theorem integral_primePairDeterminant (T q : ℝ) :
    (∫ u in (0:ℝ)..q, primePairDeterminant T u) =
      q * probeDiagonalMass T^2 - primeProbeEnergy T q := by
  have hc : Continuous (fun u => ‖primeFourierProbe T u‖^2) := by
    unfold primeFourierProbe
    fun_prop
  simp only [primePairDeterminant, primeProbeEnergy, intervalIntegral.integral_sub
    intervalIntegrable_const (hc.intervalIntegrable _ _), intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]

/-- Calibration to unit intensity divides the kernel by its diagonal and
the two-point determinant by the square of that same diagonal. -/
theorem normalized_primePairMass_tendsto {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun T => (∫ u in (0:ℝ)..q, primePairDeterminant T u) /
      probeDiagonalMass T ^ 2) atTop (𝓝 (sineGapMass q)) := by
  simp_rw [integral_primePairDeterminant]
  have hm := probeDiagonalMass_tendsto_one.pow 2
  have ht := (((tendsto_const_nhds (x := q)).mul hm).sub
    (primeProbeEnergy_tendsto hq)).div hm (by norm_num)
  change Tendsto (fun T => (q * probeDiagonalMass T ^ 2 - primeProbeEnergy T q) /
    probeDiagonalMass T ^ 2) atTop (𝓝 ((q * 1 ^ 2 - (q - sineGapMass q)) / 1 ^ 2)) at ht
  simpa using ht

/-- The remaining transfer to physical zero pairs is equality up to vanishing
error with the integrated, intensity-calibrated arithmetic determinant. -/
theorem positiveGapPCC_iff_normalized_primePairMass :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ => positiveGapMass T q -
      (∫ u in (0:ℝ)..(q:ℝ), primePairDeterminant T u) / probeDiagonalMass T ^ 2)
      atTop (𝓝 0) := by
  rw [positiveGapPCC_iff_rationalWidthLimits]
  constructor
  · intro h q hq
    simpa only [sub_self] using (h q hq).sub
      (normalized_primePairMass_tendsto (q := (q : ℝ)) (by exact_mod_cast hq.le))
  · intro h q hq
    simpa only [sub_add_cancel, zero_add] using (h q hq).add
      (normalized_primePairMass_tendsto (q := (q : ℝ)) (by exact_mod_cast hq.le))

end RiemannResearch.Analysis.MontgomeryPrimeTrace
