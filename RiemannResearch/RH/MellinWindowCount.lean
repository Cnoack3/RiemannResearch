import RiemannResearch.RH.MellinDPPIntensity
import RiemannResearch.Probability.ContinuousProjectionGenerating
import RiemannResearch.Probability.ContinuousProjectionWindowEnergy
import RiemannResearch.Probability.BoundedCountGenerating
import RiemannResearch.Probability.BoundedCountLaw

/-!
# Exact window laws, moments, and concentration of the Mellin DPP

All statements concern the actual finite law `mellinLaw n`. The compression
uses its actual orthonormal Mellin modes, and the kernel below is exactly the
arithmetic inverse-Gram kernel. Every measurable window is allowed, in
particular every bounded interval. No RH or infinite-process premise occurs.

Source: Hough--Krishnapur--Peres--Virág, Probability Surveys 3 (2006), Theorem 7,
for the general Bernoulli-count theorem; the continuous determinant bridge
and its arithmetic specialization are proved in the imported modules.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace RiemannResearch.RH.Pareto.MellinFrequency
open RiemannResearch.Probability

def mellinWindowCount (n : ℕ) (I : Set ℝ) : (Fin n → ℝ) → ℕ :=
  ContinuousProjectionDPP.windowCount I

def mellinWindowCompression (n : ℕ) (I : Set ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  ContinuousProjectionDPP.windowCompression frequencyMeasure (angularFeatures n) I

def mellinWindowEigenvalues (n : ℕ) (I : Set ℝ) : Fin n → ℝ :=
  (ContinuousProjectionDPP.windowCompression_isHermitian
    frequencyMeasure (angularFeatures n) I).eigenvalues

theorem mellinWindowEigenvalues_mem_Icc (n : ℕ) {I : Set ℝ}
    (hI : MeasurableSet I) (i : Fin n) :
    mellinWindowEigenvalues n I i ∈ Set.Icc (0 : ℝ) 1 :=
  ContinuousProjectionDPP.windowCompression_eigenvalues_mem_Icc frequencyMeasure
    (angularFeatures n) (fun i => modeFeature_memLp i.val) (angularFeatures_gram n) hI i

theorem mellinWindowCount_measurable (n : ℕ) {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable (mellinWindowCount n I) :=
  ContinuousProjectionDPP.measurable_windowCount hI

theorem mellinWindowCount_le (n : ℕ) (I : Set ℝ) (x : Fin n → ℝ) :
    mellinWindowCount n I x ≤ n :=
  ContinuousProjectionDPP.windowCount_le I x


/-- Labels count actual distinct sampled frequencies almost surely. -/
theorem mellinWindowCount_eq_configuration_count (n : ℕ) (I : Set ℝ) :
    ∀ᵐ x ∂mellinLaw n, mellinWindowCount n I x =
      ((ContinuousProjectionDPP.configuration x).filter (fun t => t ∈ I)).card := by
  filter_upwards [mellinLaw_ae_distinct n] with x hx
  simp only [mellinWindowCount, ContinuousProjectionDPP.windowCount,
    ContinuousProjectionDPP.configuration, Finset.filter_image]
  rw [Finset.card_image_of_injective _ hx]

theorem mellinWindowCount_finite_range (n : ℕ) (I : Set ℝ) :
    (Set.range (mellinWindowCount n I)).Finite := by
  apply (Set.finite_Iic n).subset
  rintro k ⟨x, rfl⟩
  exact mellinWindowCount_le n I x

/-- Exact PGF under the actual arithmetic frequency law. -/
theorem mellinWindowCount_generating (n : ℕ) {I : Set ℝ} (hI : MeasurableSet I)
    (z : ℝ) :
    (∫ x, z ^ mellinWindowCount n I x ∂mellinLaw n) =
      ∏ i, (1 - mellinWindowEigenvalues n I i + z * mellinWindowEigenvalues n I i) :=
  ContinuousProjectionDPP.windowCount_generating_spectral
    (angularFeatures n) (fun i => modeFeature_memLp i.val) (angularFeatures_gram n) hI z

/-- The complete distribution, not just its moments, is Poisson-binomial. -/
theorem mellinWindowCount_law (n : ℕ) {I : Set ℝ} (hI : MeasurableSet I) :
    (mellinLaw n).map (mellinWindowCount n I) =
      ((DPP.bernoulliSubsetLaw (mellinWindowEigenvalues n I)
        (mellinWindowEigenvalues_mem_Icc n hI)).map Finset.card).toMeasure :=
  count_law_eq_bernoulli_of_generating _ (mellinWindowCount_measurable n hI)
    (mellinWindowCount_finite_range n I) _ (mellinWindowEigenvalues_mem_Icc n hI)
    (mellinWindowCount_generating n hI)

/-- Exact expectation and variance expressed by the actual compression spectrum. -/
theorem mellinWindowCount_moments (n : ℕ) {I : Set ℝ} (hI : MeasurableSet I) :
    (∫ x, (mellinWindowCount n I x : ℝ) ∂mellinLaw n) =
        ∑ i, mellinWindowEigenvalues n I i ∧
      variance (fun x => (mellinWindowCount n I x : ℝ)) (mellinLaw n) =
        ∑ i, mellinWindowEigenvalues n I i * (1 - mellinWindowEigenvalues n I i) :=
  count_moments_of_generating _ (mellinWindowCount_measurable n hI)
    (mellinWindowCount_finite_range n I) _ (mellinWindowEigenvalues_mem_Icc n hI)
    (mellinWindowCount_generating n hI)

/-- The mean is the integral of the actual inverse-Gram Mellin intensity. -/
theorem mellinWindowCount_expectation_kernel (n : ℕ) {I : Set ℝ}
    (hI : MeasurableSet I) :
    (∫ x, (mellinWindowCount n I x : ℝ) ∂mellinLaw n) =
      ∫ t in I, (kernel n t t).re ∂frequencyMeasure := by
  rw [(mellinWindowCount_moments n hI).1]
  have ht := ContinuousProjectionDPP.windowCompression_trace frequencyMeasure
    (angularFeatures n) (fun i => modeFeature_memLp i.val) I
  rw [angularFeatures_kernel] at ht
  have hs := (ContinuousProjectionDPP.windowCompression_isHermitian
    frequencyMeasure (angularFeatures n) I).trace_eq_sum_eigenvalues
  have hint : Integrable (fun t => kernel n t t) (frequencyMeasure.restrict I) := by
    rw [← angularFeatures_kernel]
    exact (ContinuousProjectionDPP.kernel_diagonal_integrable
      (angularFeatures n) (fun i => modeFeature_memLp i.val)).integrableOn
  have hreal := integral_re hint
  change (∫ t in I, (kernel n t t).re ∂frequencyMeasure) =
    (∫ t in I, kernel n t t ∂frequencyMeasure).re at hreal
  rw [hreal]
  have h := congrArg Complex.re (hs.symm.trans ht)
  simpa [mellinWindowEigenvalues] using h

/-- Exact trace minus Hilbert--Schmidt identity for the actual window count. -/
theorem mellinWindowCount_variance_kernel (n : ℕ) {I : Set ℝ}
    (hI : MeasurableSet I) :
    variance (fun x => (mellinWindowCount n I x : ℝ)) (mellinLaw n) =
      (∫ t in I, (kernel n t t).re ∂frequencyMeasure) -
        ∫ t in I, ∫ u in I, ‖kernel n t u‖ ^ 2 ∂frequencyMeasure ∂frequencyMeasure := by
  rw [← mellinWindowCount_expectation_kernel n hI,
    (mellinWindowCount_moments n hI).1, (mellinWindowCount_moments n hI).2]
  have hh := (ContinuousProjectionDPP.windowCompression_isHermitian
    frequencyMeasure (angularFeatures n) I).sum_eigenvalue_variance_eq_trace_sub_hilbertSchmidt
  rw [(ContinuousProjectionDPP.windowCompression_isHermitian
    frequencyMeasure (angularFeatures n) I).trace_eq_sum_eigenvalues] at hh
  have he := ContinuousProjectionDPP.windowCompression_hilbertSchmidt_eq_kernel_integral
    frequencyMeasure (angularFeatures n) (fun i => modeFeature_memLp i.val) I
  rw [angularFeatures_kernel] at he
  rw [he] at hh
  simpa [mellinWindowEigenvalues] using congrArg Complex.re hh

/-- The variance is exactly the kernel energy that crosses the window boundary. -/
theorem mellinWindowCount_variance_boundary (n : ℕ) {I : Set ℝ}
    (hI : MeasurableSet I) :
    variance (fun x => (mellinWindowCount n I x : ℝ)) (mellinLaw n) =
      ∫ t in I, ∫ u in Iᶜ, ‖kernel n t u‖ ^ 2 ∂frequencyMeasure ∂frequencyMeasure := by
  rw [(mellinWindowCount_moments n hI).2]
  have h := ContinuousProjectionDPP.window_kernel_boundary_eq_eigenvalue_variance
    frequencyMeasure (angularFeatures n) (fun i => modeFeature_memLp i.val)
    (angularFeatures_gram n) hI
  rw [angularFeatures_kernel] at h
  exact h.symm

theorem mellinWindowCount_variance_bounds (n : ℕ) {I : Set ℝ}
    (hI : MeasurableSet I) :
    variance (fun x => (mellinWindowCount n I x : ℝ)) (mellinLaw n) ≤
        ∑ i, mellinWindowEigenvalues n I i ∧
      variance (fun x => (mellinWindowCount n I x : ℝ)) (mellinLaw n) ≤
        (n : ℝ) - ∑ i, mellinWindowEigenvalues n I i ∧
      variance (fun x => (mellinWindowCount n I x : ℝ)) (mellinLaw n) ≤ (n : ℝ) / 4 := by
  rw [(mellinWindowCount_moments n hI).2]
  simpa using bernoulli_variance_bounds _ (mellinWindowEigenvalues_mem_Icc n hI)

/-- Exact Chernoff upper tail, valid for every tilt and therefore optimizable. -/
theorem mellinWindowCount_upper_tail (n : ℕ) {I : Set ℝ}
    (hI : MeasurableSet I) (a t : ℝ) (ht : 0 ≤ t) :
    (mellinLaw n).real {x | a ≤ (mellinWindowCount n I x : ℝ)} ≤
      Real.exp (-t * a) *
        ∏ i, (1 - mellinWindowEigenvalues n I i +
          Real.exp t * mellinWindowEigenvalues n I i) :=
  count_upper_tail_le_product
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (mellinWindowCount_measurable n hI))
    (mellinWindowCount_le n I) (mellinWindowCount_generating n hI) a t ht

/-- Exact Chernoff lower tail for the same actual law and spectrum. -/
theorem mellinWindowCount_lower_tail (n : ℕ) {I : Set ℝ}
    (hI : MeasurableSet I) (a t : ℝ) (ht : 0 ≤ t) :
    (mellinLaw n).real {x | (mellinWindowCount n I x : ℝ) ≤ a} ≤
      Real.exp (t * a) *
        ∏ i, (1 - mellinWindowEigenvalues n I i +
          Real.exp (-t) * mellinWindowEigenvalues n I i) :=
  count_lower_tail_le_product
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (mellinWindowCount_measurable n hI))
    (mellinWindowCount_le n I) (mellinWindowCount_generating n hI) a t ht


/-- Exact bounded-window hole probability under the actual Mellin law. -/
theorem mellinWindowCount_hole (n : ℕ) {I : Set ℝ} (hI : MeasurableSet I) :
    (mellinLaw n).real {x | mellinWindowCount n I x = 0} =
      ∏ i, (1 - mellinWindowEigenvalues n I i) :=
  count_hole_probability (mellinWindowCount_measurable n hI)
    (mellinWindowCount_generating n hI)

theorem mellinWindowCount_hole_le_exp (n : ℕ) {I : Set ℝ} (hI : MeasurableSet I) :
    (mellinLaw n).real {x | mellinWindowCount n I x = 0} ≤
      Real.exp (-(∫ t in I, (kernel n t t).re ∂frequencyMeasure)) := by
  rw [← mellinWindowCount_expectation_kernel n hI,
    (mellinWindowCount_moments n hI).1]
  exact count_hole_probability_le_exp (mellinWindowCount_measurable n hI)
    (mellinWindowEigenvalues_mem_Icc n hI) (mellinWindowCount_generating n hI)

/-- An explicit first-mode arithmetic lower bound on the expected count,
independent of the larger arithmetic rank. -/
theorem mellinWindowCount_expectation_ge_first_mode (n : ℕ) (hn : 0 < n)
    {I : Set ℝ} (hI : MeasurableSet I) :
    (∫ t in I, ‖modeFeature 0 t‖ ^ 2 ∂frequencyMeasure) ≤
      ∫ x, (mellinWindowCount n I x : ℝ) ∂mellinLaw n := by
  have hi (m : ℕ) : Integrable (fun t => (kernel m t t).re) frequencyMeasure := by
    rw [← angularFeatures_kernel]
    exact (ContinuousProjectionDPP.kernel_diagonal_integrable
      (angularFeatures m) (fun i => modeFeature_memLp i.val)).re
  have hz : Integrable (fun t => ‖modeFeature 0 t‖ ^ 2) frequencyMeasure := by
    simpa [diagonal_eq_sum_norm_sq] using hi 1
  rw [mellinWindowCount_expectation_kernel n hI]
  exact integral_mono hz.integrableOn (hi n).integrableOn (first_mode_le_diagonal n hn)


/-- Exact arithmetic exponent supplied by the normalized conductor-two mode. -/
theorem firstModeWindowMass_eq_arithmetic (I : Set ℝ) :
    (∫ t in I, ‖modeFeature 0 t‖ ^ 2 ∂frequencyMeasure) =
      (4 / Real.log 2) *
        ∫ t in I, ‖zetaEnvelope t‖ ^ 2 * ‖residueSymbol 0 t‖ ^ 2 ∂frequencyMeasure := by
  have he (t : ℝ) : ‖modeFeature 0 t‖ ^ 2 =
      (4 / Real.log 2) * (‖zetaEnvelope t‖ ^ 2 * ‖residueSymbol 0 t‖ ^ 2) := by
    rw [modeFeature_zero_formula, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, div_pow,
      Real.sq_sqrt (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
    ring
  simp_rw [he]
  exact integral_const_mul _ _

/-- Explicit nontrivial arithmetic hole bound for every positive rank.
The first-mode formula expresses this exponent as
(4/log 2) times the integral of |zeta(s)/s|² |1/2-2^(-s)|². -/
theorem mellinWindowCount_hole_first_mode (n : ℕ) (hn : 0 < n)
    {I : Set ℝ} (hI : MeasurableSet I) :
    (mellinLaw n).real {x | mellinWindowCount n I x = 0} ≤
      Real.exp (-((4 / Real.log 2) *
        ∫ t in I, ‖zetaEnvelope t‖ ^ 2 * ‖residueSymbol 0 t‖ ^ 2 ∂frequencyMeasure)) := by
  rw [← firstModeWindowMass_eq_arithmetic I]
  apply (mellinWindowCount_hole_le_exp n hI).trans
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff, ← mellinWindowCount_expectation_kernel n hI]
  exact mellinWindowCount_expectation_ge_first_mode n hn hI

end RiemannResearch.RH.Pareto.MellinFrequency
