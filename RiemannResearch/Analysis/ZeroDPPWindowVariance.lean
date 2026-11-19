import RiemannResearch.Probability.ZeroOrdinatePrimeDPP
import RiemannResearch.Analysis.ZeroDPPMontgomery
import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion
import Mathlib.Probability.Moments.Variance

/-!
# Fixed-width Montgomery windows of a sampled ordinate transversal

For the saturated zero-label law, multiplicity weighting reconstructs the
clipped actual window count at every height, width, and position on a single
event of probability one. The normalized variance taken over translations
is exactly the actual Montgomery window variance. At a fixed window the
variance taken over label selection is zero.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ZeroDPPCorrelation
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open MontgomeryPositiveGap
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- Count a translated, height-clipped window using the selected labels and
their actual ordinate multiplicities. -/
def sampledWindowCount (x : Site → Bool) (T h t : ℝ) : ℝ :=
  ∑ c : Copies T, if x (liftCopy T c) = true then
    (actualOrdinateMultiplicity T (copyOrdinate T c) : ℝ) *
      OrdinateWindowVariance.windowPulse T h (copyOrdinate T c) t else 0

/-- All widths, centres, and cutoffs are recovered on one common event. -/
theorem sampledWindowCount_eq_ae (q : ℕ → ℝ) (b : ℝ) (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi)
    (hq : ContainsHarmonics q b) :
    ∀ᵐ x ∂limitingLaw q, ∀ T h t : ℝ, sampledWindowCount x T h t = actualWindowCount T h t := by
  filter_upwards [exactly_one_per_ordinate_ae q b hb hbπ hq] with x hx
  intro T h t
  exact sum_weighted_ordinate_of_transversal x hx T
    (fun τ => OrdinateWindowVariance.windowPulse T h τ t)

/-- The fixed-window count is deterministic under random label selection. -/
theorem variance_sampledWindowCount_zero (q : ℕ → ℝ) (b : ℝ) (hb : 0 < b)
    (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) (T h t : ℝ) :
    ProbabilityTheory.variance (fun x => sampledWindowCount x T h t) (limitingLaw q) = 0 := by
  have he : (fun x => sampledWindowCount x T h t) =ᵐ[limitingLaw q] fun _ => actualWindowCount T h t :=
    (sampledWindowCount_eq_ae q b hb hbπ hq).mono fun _ hx => hx T h t
  rw [ProbabilityTheory.variance_congr he, ProbabilityTheory.variance_eq_integral
    measurable_const.aemeasurable]
  simp

/-- Translation variance of the reconstructed window count, with the exact
finite-height mean and the same clipping conventions as the actual count. -/
def sampledUnfoldedWindowVariance (x : Site → Bool) (T R : ℝ) : ℝ :=
  (∫ t : ℝ, (sampledWindowCount x T (R / (Real.log T / (2 * Real.pi))) t -
    unfoldedWindowMean T R * OrdinateWindowVariance.pulse 0 T t) ^ 2) / T

/-- The translated-window variances of the sample and of the true zero
occurrences agree at every finite height and every width almost surely. -/
theorem sampledUnfoldedWindowVariance_eq_ae (q : ℕ → ℝ) (b : ℝ) (hb : 0 < b)
    (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) :
    ∀ᵐ x ∂limitingLaw q, ∀ T R : ℝ,
      sampledUnfoldedWindowVariance x T R = unfoldedWindowVariance T R := by
  filter_upwards [sampledWindowCount_eq_ae q b hb hbπ hq] with x hx
  intro T R
  simp only [sampledUnfoldedWindowVariance, hx, unfoldedWindowVariance,
    actualCenteredCount, OrdinateWindowVariance.centeredCount, actualWindowCount]

/-- The positive rational-width sine-variance input can be tested on this
single sampled process. No extra variance or independence input is needed. -/
theorem rationalSineWindowVariance_iff_sampled (q : ℕ → ℝ) (b : ℝ) (hb : 0 < b)
    (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) :
    RationalSineWindowVariance ↔ ∀ᵐ x ∂limitingLaw q, ∀ R : ℚ, 0 < R →
      Tendsto (fun T => sampledUnfoldedWindowVariance x T R) atTop
        (𝓝 (sineWindowEnergy R - (R : ℝ) ^ 2)) := by
  have he := sampledUnfoldedWindowVariance_eq_ae q b hb hbπ hq
  constructor
  · intro h
    filter_upwards [he] with x hx
    simpa only [hx, RationalSineWindowVariance] using h
  · intro h
    obtain ⟨x, hx, hlim⟩ := (he.and h).exists
    simpa only [hx, RationalSineWindowVariance] using hlim

/-- Rational-width sampled translation variance implies both ordinary PCC
and negligible expected logarithmic deletions relative to the zero count. -/
theorem pcc_and_relativeVacancy_of_sampled_variance (q : ℕ → ℝ) (b : ℝ) (hb : 0 < b)
    (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b)
    (h : ∀ᵐ x ∂limitingLaw q, ∀ R : ℚ, 0 < R →
      Tendsto (fun T => sampledUnfoldedWindowVariance x T R) atTop
        (𝓝 (sineWindowEnergy R - (R : ℝ) ^ 2))) :
    PositiveGapPCC ∧ Tendsto (fun T : ℝ =>
      cutoffVacancy (fun k => Real.log ((k : ℝ) + 1)) T / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
  have hf := (rationalSineWindowVariance_iff_sampled q b hb hbπ hq).mpr h
  exact ⟨positiveGapPCC_of_rationalSineWindowVariance hf,
    logarithmic_relativeVacancy_tendsto_zero_iff.mpr (density_one_of_rationalSineWindowVariance hf).1⟩

/-- Sum of the label vacancy probabilities in the actual clipped window
with left endpoint t and physical width h. -/
def windowVacancy (q : ℕ → ℝ) (T h t : ℝ) : ℝ :=
  ∑ c : Copies T, (1 - limitingKernel q (liftCopy T c) (liftCopy T c)) *
    OrdinateWindowVariance.windowPulse T h (copyOrdinate T c) t

/-- Once the width is below all included ordinates, each label contributes
its vacancy times exactly h to the translation integral. -/
theorem integral_windowVacancy (q : ℕ → ℝ) (T h : ℝ) (hh : 0 ≤ h)
    (hfloor : ∀ c : Copies T, h ≤ copyOrdinate T c) :
    (∫ t : ℝ, windowVacancy q T h t) = cutoffVacancy q T * h := by
  classical
  unfold windowVacancy
  rw [integral_finsetSum]
  · rw [cutoffVacancy, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul, OrdinateWindowVariance.windowPulse,
      OrdinateWindowVariance.integral_pulse]
    have hT : copyOrdinate T c ≤ T := (mem_cutoff.mp c.1.2).2.2
    rw [min_eq_right hT, max_eq_right (sub_nonneg.mpr (hfloor c)), sub_sub_cancel, max_eq_left hh]
  · intro c _
    exact (OrdinateWindowVariance.windowPulse_integrable T h (copyOrdinate T c)).const_mul _

/-- Height-normalized translation mean of the vacancy at unfolded width R. -/
def meanWindowVacancy (q : ℕ → ℝ) (T R : ℝ) : ℝ :=
  (∫ t : ℝ, windowVacancy q T (R / (Real.log T / (2 * Real.pi))) t) / T

/-- The averaged microscopic vacancy is exactly the global vacancy fraction
times the actual finite-height mean window count, uniformly in the dictionary. -/
theorem eventually_meanWindowVacancy_eq {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ T : ℝ in atTop, ∀ q : ℕ → ℝ, meanWindowVacancy q T R =
      (cutoffVacancy q T / (Ncount 0 T : ℝ)) * unfoldedWindowMean T R := by
  obtain ⟨d, hd, hfloor⟩ := exists_ordinate_floor
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.pi * R / d),
    tendsto_count_div_mainTerm.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with T hT hL hcount q
  have hTp := zero_lt_one.trans hT
  have hscale := div_pos (Real.log_pos hT) (show 0 < 2 * Real.pi by positivity)
  have hwidth : R / (Real.log T / (2 * Real.pi)) ≤ d := by
    apply (div_le_iff₀ hscale).2
    have h := (div_le_iff₀ hd).1 hL
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith only [h]
  have hN : (Ncount 0 T : ℝ) ≠ 0 := by intro hz; simp [hz] at hcount
  rw [meanWindowVacancy, integral_windowVacancy q T _ (div_nonneg hR hscale.le)
    (fun c => hwidth.trans (hfloor T c)), unfoldedWindowMean]
  field_simp [hN, hTp.ne', hscale.ne']

/-- At any one fixed positive unfolded width, mean microscopic vacancy tends
to zero exactly when the fraction of deleted labels does, even for moving
dictionaries. -/
theorem meanWindowVacancy_tendsto_zero_iff (q : ℝ → ℕ → ℝ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T => meanWindowVacancy (q T) T R) atTop (𝓝 0) ↔
      Tendsto (fun T => cutoffVacancy (q T) T / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
  have he := (eventually_meanWindowVacancy_eq hR.le).mono fun T ht => ht (q T)
  have hm := unfoldedWindowMean_tendsto R
  constructor
  · intro h
    have hh := h.div hm hR.ne'
    rw [zero_div] at hh
    apply hh.congr'
    filter_upwards [he, hm.eventually (lt_mem_nhds hR)] with T heT hpos
    change meanWindowVacancy (q T) T R / unfoldedWindowMean T R = _
    rw [heT]
    exact mul_div_cancel_right₀ _ hpos.ne'
  · intro h
    have hh := h.mul hm
    rw [zero_mul] at hh
    exact hh.congr' (he.mono (fun _ hT => hT.symm))

/-- For the complete logarithmic law the moving-window mean vacancy
condition is equivalent to density one of simple critical zeros. -/
theorem logarithmic_meanWindowVacancy_iff_simpleCritical_density {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T => meanWindowVacancy (fun k => Real.log ((k : ℝ) + 1)) T R) atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  (meanWindowVacancy_tendsto_zero_iff (fun _ k => Real.log ((k : ℝ) + 1)) hR).trans
    logarithmic_relativeVacancy_tendsto_zero_iff

private theorem log_two_step_bounds : 0 < Real.log 2 ∧ Real.log 2 ≤ 2 * Real.pi :=
  ⟨Real.log_pos (by norm_num), by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2), Real.pi_gt_three]⟩

/-- Prime frequencies alone reconstruct all actual positive gaps, clipped
window counts and translated window variances on one probability-one event. -/
theorem prime_ordinate_statistics_ae :
    ∀ᵐ x ∂limitingLaw primeFrequencies,
      (∀ T u : ℝ, sampledPositiveGapMass x T u = positiveGapMass T u) ∧
      (∀ T h t : ℝ, sampledWindowCount x T h t = actualWindowCount T h t) ∧
      (∀ T R : ℝ, sampledUnfoldedWindowVariance x T R = unfoldedWindowVariance T R) := by
  rw [primeFrequencies_limitingLaw]
  obtain ⟨hp, hb⟩ := log_two_step_bounds
  exact (sampledPositiveGapMass_eq_ae _ _ hp hb logarithmic_containsHarmonics).and
    ((sampledWindowCount_eq_ae _ _ hp hb logarithmic_containsHarmonics).and
      (sampledUnfoldedWindowVariance_eq_ae _ _ hp hb logarithmic_containsHarmonics))

/-- Ordinary positive-gap PCC on the unconditionally constructed pure-prime DPP. -/
theorem positiveGapPCC_iff_prime_sampled :
    PositiveGapPCC ↔ ∀ᵐ x ∂limitingLaw primeFrequencies, ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop, ∀ u ∈ Set.Icc a b,
        |sampledPositiveGapMass x T u - sineGapMass u| ≤ η := by
  rw [primeFrequencies_limitingLaw]
  exact positiveGapPCC_iff_sampled _ _ log_two_step_bounds.1 log_two_step_bounds.2
    logarithmic_containsHarmonics

/-- The rational-width sine-variance input can be stated on the pure-prime DPP. -/
theorem rationalSineWindowVariance_iff_prime_sampled :
    RationalSineWindowVariance ↔ ∀ᵐ x ∂limitingLaw primeFrequencies, ∀ R : ℚ, 0 < R →
      Tendsto (fun T => sampledUnfoldedWindowVariance x T R) atTop
        (𝓝 (sineWindowEnergy R - (R : ℝ) ^ 2)) := by
  rw [primeFrequencies_limitingLaw]
  exact rationalSineWindowVariance_iff_sampled _ _ log_two_step_bounds.1 log_two_step_bounds.2
    logarithmic_containsHarmonics

end RiemannResearch.Analysis.ZeroDPPCorrelation
