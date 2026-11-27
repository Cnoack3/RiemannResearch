import RiemannResearch.Analysis.MontgomeryGapReconstruction
import RiemannResearch.Analysis.GaussianGapTests
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic.FunProp

/-!
# Physical two-point tests from the signed Fourier reconstruction

The Fourier convention is `cos (2π h x)`. The probe and its coefficients
can be prescribed before any individual zero locations are known.
Every frequency is retained by using the explicit Borel Taylor order.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- All ordered occurrence pairs, divided by the original occurrence count. -/
def fullGapSpectrum (T u : ℝ) : ℝ :=
  (∑ p : Copies T, ∑ q : Copies T, Real.cos ((copyOrdinate T p - copyOrdinate T q) * u)) /
    (Zeta23.Ncount 0 T : ℝ)

def reconstructedGapSpectrum (T u b : ℝ) : ℝ :=
  ‖reconstructedOrdinateSum T u (gapReconstructionOrder T u b)‖ ^ 2 / (Zeta23.Ncount 0 T : ℝ)

/-- Inverse cosine transform with cycles per unit displacement. -/
def cosineGapProbe (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ h : ℝ, Real.cos (2 * Real.pi * h * x) * w h

private theorem measurable_reconstructedGapSpectrum (T b : ℝ) :
    Measurable (fun u => reconstructedGapSpectrum T u b) := by
  have hJ : Measurable (fun u => gapReconstructionOrder T u b) := by
    unfold gapReconstructionOrder
    apply Measurable.nat_ceil
    fun_prop
  have hrec : Measurable (fun z : ℝ × ℕ => reconstructedOrdinateSum T z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro j
    change Measurable (fun u : ℝ => reconstructedOrdinateSum T u j)
    apply Continuous.measurable
    unfold reconstructedOrdinateSum landauSum evenHorizontalMoment sum ZeroOrdinate.phase
    fun_prop
  have h := hrec.comp (measurable_id.prodMk hJ)
  change Measurable (fun u => ‖reconstructedOrdinateSum T u (gapReconstructionOrder T u b)‖^2 /
    (Zeta23.Ncount 0 T : ℝ))
  exact (h.norm.pow_const 2).div_const _

theorem fullGapSpectrum_sub_reconstructed_le (T u b : ℝ) (hb : 0 ≤ b) :
    |fullGapSpectrum T u - reconstructedGapSpectrum T u b| ≤ 3 * Real.exp (-b) := by
  unfold fullGapSpectrum reconstructedGapSpectrum
  rw [← sub_div]
  exact gap_reconstruction_exp_error T u b _ hb (gapReconstructionOrder_sufficient T u b)

/-- Exact finite Fourier pairing, including every occurrence on the diagonal. -/
theorem fullGapSpectrum_cosine_pairing (T L : ℝ) {w : ℝ → ℝ} (hw : Integrable w) :
    Integrable (fun h => fullGapSpectrum T (2 * Real.pi * h * L) * w h) ∧
    (∫ h : ℝ, fullGapSpectrum T (2 * Real.pi * h * L) * w h) =
      (∑ p : Copies T, ∑ q : Copies T,
        cosineGapProbe w (L * (copyOrdinate T p - copyOrdinate T q))) /
        (Zeta23.Ncount 0 T : ℝ) := by
  let F := fun (p q : Copies T) (h : ℝ) =>
    Real.cos (2 * Real.pi * h * (L * (copyOrdinate T p - copyOrdinate T q))) * w h
  have hi (p q : Copies T) : Integrable (F p q) := by
    apply hw.bdd_mul (c := 1)
    · exact (show Continuous (fun h : ℝ =>
        Real.cos (2 * Real.pi * h * (L * (copyOrdinate T p - copyOrdinate T q)))) by
          fun_prop).aestronglyMeasurable
    · exact Eventually.of_forall fun h => by
        simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _
  have he (h : ℝ) : fullGapSpectrum T (2 * Real.pi * h * L) * w h =
      (∑ p : Copies T, ∑ q : Copies T, F p q h) / (Zeta23.Ncount 0 T : ℝ) := by
    unfold fullGapSpectrum
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    dsimp [F]
    congr 2
    ring
  simp_rw [he]
  have hp (p : Copies T) : Integrable (fun h => ∑ q, F p q h) :=
    integrable_finsetSum _ (fun q _ => hi p q)
  constructor
  · exact (integrable_finsetSum _ (fun p _ => hp p)).div_const _
  · rw [integral_div, integral_finsetSum _ (fun p _ => hp p)]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [integral_finsetSum _ (fun q _ => hi p q)]
    rfl

/-- For an integrable Fourier weight, the count-normalized error of the
physical pair test is at most three times the L¹ mass times exp(-b).
The order varies measurably with frequency. -/
theorem reconstructed_cosine_gap_test (T L b : ℝ) (hb : 0 ≤ b)
    {w : ℝ → ℝ} (hw : Integrable w) :
    Integrable (fun h => reconstructedGapSpectrum T (2 * Real.pi * h * L) b * w h) ∧
    |(∑ p : Copies T, ∑ q : Copies T,
        cosineGapProbe w (L * (copyOrdinate T p - copyOrdinate T q))) / (Zeta23.Ncount 0 T : ℝ) -
      ∫ h : ℝ, reconstructedGapSpectrum T (2 * Real.pi * h * L) b * w h| ≤
        (3 * Real.exp (-b)) * ∫ h : ℝ, |w h| := by
  let u := fun h : ℝ => 2 * Real.pi * h * L
  let A := fun h : ℝ => fullGapSpectrum T (u h)
  let R := fun h : ℝ => reconstructedGapSpectrum T (u h) b
  have hu : Measurable u := by dsimp [u]; fun_prop
  have hA : Measurable A := by dsimp [A, u, fullGapSpectrum]; fun_prop
  have hR : Measurable R := (measurable_reconstructedGapSpectrum T b).comp hu
  obtain ⟨hIA, hpair⟩ := fullGapSpectrum_cosine_pairing T L hw
  have hbound (h : ℝ) : ‖A h - R h‖ ≤ 3 * Real.exp (-b) :=
    fullGapSpectrum_sub_reconstructed_le T (u h) b hb
  have hID : Integrable (fun h => (A h - R h) * w h) :=
    hw.bdd_mul (hA.sub hR).aestronglyMeasurable (Eventually.of_forall hbound)
  have hIR : Integrable (fun h => R h * w h) := by
    apply (hIA.sub hID).congr (Eventually.of_forall fun h => ?_)
    change A h * w h - (A h - R h) * w h = R h * w h
    ring
  refine ⟨hIR, ?_⟩
  rw [← hpair, ← integral_sub hIA hIR]
  change |∫ h : ℝ, A h * w h - R h * w h| ≤ _
  simp_rw [← sub_mul]
  calc
    _ ≤ ∫ h : ℝ, ‖(A h - R h) * w h‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ h : ℝ, (3 * Real.exp (-b)) * |w h| := by
      apply integral_mono hID.norm (hw.norm.const_mul _)
      intro h
      change ‖(A h - R h) * w h‖ ≤ (3 * Real.exp (-b)) * ‖w h‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound h) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The reduced factorial statistic excludes only the two labels being equal.
Distinct labels with the same ordinate remain in the inner sum. -/
def factorialCosineGapTest (T L : ℝ) (w : ℝ → ℝ) : ℝ := by
  classical
  exact (∑ p : Copies T, ∑ q ∈ Finset.univ.erase p,
    cosineGapProbe w (L * (copyOrdinate T p - copyOrdinate T q))) / (Zeta23.Ncount 0 T : ℝ)

theorem factorialCosineGapTest_eq (T L : ℝ) (w : ℝ → ℝ) (hN : 0 < Zeta23.Ncount 0 T) :
    factorialCosineGapTest T L w =
      (∑ p : Copies T, ∑ q : Copies T,
        cosineGapProbe w (L * (copyOrdinate T p - copyOrdinate T q))) / (Zeta23.Ncount 0 T : ℝ) -
      cosineGapProbe w 0 := by
  classical
  have hr (p : Copies T) : (∑ q ∈ Finset.univ.erase p,
      cosineGapProbe w (L * (copyOrdinate T p - copyOrdinate T q))) + cosineGapProbe w 0 =
      ∑ q : Copies T, cosineGapProbe w (L * (copyOrdinate T p - copyOrdinate T q)) := by
    simpa only [sub_self, mul_zero] using Finset.sum_erase_add
      (s := Finset.univ) (fun q : Copies T =>
        cosineGapProbe w (L * (copyOrdinate T p - copyOrdinate T q))) (Finset.mem_univ p)
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset (Copies T))) rfl (fun p _ => hr p)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul] at hh
  have hn : (Zeta23.Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold factorialCosineGapTest
  field_simp [hn]
  linarith only [hh]

/-- The Fourier reconstruction also holds for the full reduced factorial
statistic, including the mass of ties between distinct occurrences. -/
theorem reconstructed_factorial_cosine_gap_test (T L b : ℝ) (hb : 0 ≤ b)
    (hN : 0 < Zeta23.Ncount 0 T) {w : ℝ → ℝ} (hw : Integrable w) :
    |factorialCosineGapTest T L w -
      ((∫ h : ℝ, reconstructedGapSpectrum T (2 * Real.pi * h * L) b * w h) - cosineGapProbe w 0)| ≤
        (3 * Real.exp (-b)) * ∫ h : ℝ, |w h| := by
  rw [factorialCosineGapTest_eq T L w hN, sub_sub_sub_cancel_right]
  exact (reconstructed_cosine_gap_test T L b hb hw).2

/-- At the physical unfolding the actual factorial statistic and its
reconstructed Fourier integral have the same limit whenever either has one. -/
theorem factorialCosineGapTest_tendsto_iff_reconstructed {w : ℝ → ℝ}
    (hw : Integrable w) (y : ℝ) :
    Tendsto (fun T : ℝ => factorialCosineGapTest T (Real.log T / (2 * Real.pi)) w)
        atTop (𝓝 y) ↔
      Tendsto (fun T : ℝ =>
        (∫ h : ℝ, reconstructedGapSpectrum T (2 * Real.pi * h * (Real.log T / (2 * Real.pi)))
          (Real.log T) * w h) - cosineGapProbe w 0) atTop (𝓝 y) := by
  let A := fun T : ℝ => factorialCosineGapTest T (Real.log T / (2 * Real.pi)) w
  let R := fun T : ℝ => (∫ h : ℝ, reconstructedGapSpectrum T
    (2 * Real.pi * h * (Real.log T / (2 * Real.pi))) (Real.log T) * w h) - cosineGapProbe w 0
  have hlim : Tendsto (fun T : ℝ => T⁻¹ * (3 * ∫ h : ℝ, |w h|)) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_inv_atTop_zero.mul_const (3 * ∫ h : ℝ, |w h|))
  have hd : Tendsto (fun T : ℝ => A T - R T) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_count_pos, eventually_gt_atTop (1 : ℝ)] with T hN hT
    have hh := reconstructed_factorial_cosine_gap_test T (Real.log T / (2 * Real.pi))
      (Real.log T) (Real.log_pos hT).le hN hw
    rw [Real.exp_neg, Real.exp_log (zero_lt_one.trans hT)] at hh
    change |A T - R T| ≤ _
    calc
      _ ≤ _ := hh
      _ = _ := by ring
  change Tendsto A atTop (𝓝 y) ↔ Tendsto R atTop (𝓝 y)
  constructor
  · intro hA
    simpa only [sub_sub_cancel, sub_zero] using hA.sub hd
  · intro hR
    simpa only [sub_add_cancel, zero_add] using hd.add hR

/-- The finite full factorial measure in the signed displacement variable.
Each label is omitted only from its own row. -/
def factorialGapMeasure (T L : ℝ) : Measure ℝ := by
  classical
  exact (Zeta23.Ncount 0 T : ℝ≥0)⁻¹ •
    ∑ p : Copies T, ∑ q ∈ Finset.univ.erase p,
      Measure.dirac (L * (copyOrdinate T p - copyOrdinate T q))

theorem integral_factorialGapMeasure (T L : ℝ) (g : ℝ → ℝ) :
    Integrable g (factorialGapMeasure T L) ∧
    (∫ x, g x ∂(factorialGapMeasure T L)) =
      (∑ p : Copies T, ∑ q ∈ Finset.univ.erase p,
        g (L * (copyOrdinate T p - copyOrdinate T q))) / (Zeta23.Ncount 0 T : ℝ) := by
  classical
  let d := fun p q : Copies T => L * (copyOrdinate T p - copyOrdinate T q)
  have hi (p q : Copies T) : Integrable g (Measure.dirac (d p q)) := by
    apply integrable_dirac
    simp
  have hr (p : Copies T) : Integrable g (∑ q ∈ Finset.univ.erase p, Measure.dirac (d p q)) :=
    integrable_finsetSum_measure.mpr fun q _ => hi p q
  unfold factorialGapMeasure
  refine ⟨(integrable_finsetSum_measure.mpr (fun p _ => hr p)).smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, integral_finsetSum_measure (fun p _ => hr p)]
  simp_rw [integral_finsetSum_measure (fun q _ => hi _ q), integral_dirac]
  simp [d, NNReal.smul_def, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The target Lebesgue-reference reduced sine pair measure. -/
def sineFactorialGapMeasure : Measure ℝ :=
  volume.withDensity (fun x : ℝ => ENNReal.ofReal (1 - Real.sinc (Real.pi * x)^2))

private theorem integrable_weight_sineFactorialGapMeasure :
    Integrable GaussianGapTests.weight sineFactorialGapMeasure := by
  have hle : sineFactorialGapMeasure ≤ volume := by
    calc
      _ ≤ volume.withDensity (1 : ℝ → ℝ≥0∞) := by
        apply withDensity_mono
        exact ae_of_all _ fun x => by
          change ENNReal.ofReal (1 - Real.sinc (Real.pi * x)^2) ≤ 1
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (sub_le_self _ (sq_nonneg _))
      _ = _ := withDensity_one
  apply Integrable.mono_measure _ hle
  change Integrable (fun x : ℝ => Real.exp (-(x ^ 2))) (volume : Measure ℝ)
  simpa using (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1))

/-- The only asymptotic input is agreement at all positive integer Gaussian
powers. It gives the sine answer on all continuous compactly supported even
tests of actual unfolded displacements. -/
theorem actual_sine_gap_tests_of_gaussian_moments
    (hm : ∀ n : ℕ, Tendsto (fun T : ℝ =>
      ∫ x, GaussianGapTests.weight x ^ (n + 1)
        ∂(factorialGapMeasure T (Real.log T / (2 * Real.pi))))
      atTop (𝓝 (∫ x, GaussianGapTests.weight x ^ (n + 1) ∂sineFactorialGapMeasure)))
    {g : ℝ → ℝ} (hg : Continuous g) (he : ∀ x, g (-x) = g x)
    {R : ℝ} (hR : 0 ≤ R) (hz : ∀ x, R ≤ |x| → g x = 0) :
    Tendsto (fun T : ℝ => ∫ x, g x ∂(factorialGapMeasure T (Real.log T / (2 * Real.pi))))
      atTop (𝓝 (∫ x, g x ∂sineFactorialGapMeasure)) := by
  exact GaussianGapTests.tendsto_even_gap_integral_of_gaussian_moments
    _ _ (fun T => (integral_factorialGapMeasure T _ _).1)
    integrable_weight_sineFactorialGapMeasure hm hg he hR hz

#print axioms actual_sine_gap_tests_of_gaussian_moments
#print axioms reconstructed_factorial_cosine_gap_test
#print axioms factorialCosineGapTest_tendsto_iff_reconstructed
end RiemannResearch.Analysis.ActualZeroOrdinate
