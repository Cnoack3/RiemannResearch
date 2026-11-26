import RiemannResearch.Analysis.MontgomerySignedCesaroTrace

/-!
# Bounded moving widths and three signed Cesàro measurements

We use the actual sampled argument, with endpoint clipping and occurrence
multiplicity as in `MontgomerySignedCesaroTrace`. The estimates for the prime
probe and the sampled smooth count allow a compact test down to arbitrarily
small positive widths. Three signed Cesàro measurements also give an eventual
pointwise bound, without assuming pair correlation.
-/

noncomputable section

namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter Set MontgomeryPositiveGap ActualZeroOrdinate ActualZeroDiscrepancy
open scoped Topology

/-- Positive-gap PCC is equivalent to simultaneous cancellation of the signed
prime–zero trace at all positive real widths in each bounded interval. -/
theorem positiveGapPCC_iff_uniformSignedTrace :
    PositiveGapPCC ↔ ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ T : ℝ in atTop, ∀ q ∈ Ioc (0 : ℝ) R,
        |sampledArgumentIncrement T q + primeProbeEnergy T q| ≤ ε := by
  constructor
  · intro hp R hR ε hε
    let d := min R (ε / 4)
    have hd : 0 < d := lt_min hR (by positivity)
    have hdR : d ≤ R := min_le_left _ _
    have hdε : d ≤ ε / 4 := min_le_right _ _
    have hG₀ : sineGapMass 0 = 0 := by simp [sineGapMass]
    have hGd := (sineGapMass_increment_bounds hd.le).2
    rw [hG₀, sub_zero, sub_zero] at hGd
    filter_upwards [hp d R hd hdR (ε / 4) (by positivity),
      eventually_signedTrace_gap_error_uniform hR (show 0 < ε / 2 by positivity),
      eventually_gt_atTop (1 : ℝ)] with T hg hs hT
    intro q hq
    have herr : |positiveGapMass T q - sineGapMass q| ≤ ε / 2 := by
      by_cases hdq : d ≤ q
      · exact (hg q ⟨hdq,hq.2⟩).trans (by linarith)
      · have hqd := le_of_lt (lt_of_not_ge hdq)
        have hp₀ := positiveGapMass_nonneg hT q
        have hP := (positiveGapMass_mono hT) hqd
        have hG := sineGapMass_mono hqd
        have hGq := sineGapMass_mono hq.1.le
        rw [hG₀] at hGq
        have hPd := (abs_le.mp (hg d ⟨le_rfl, hdR⟩)).2
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h := abs_le.mp (hs q hq)
    have e := abs_le.mp herr
    exact abs_le.mpr ⟨by linarith only [h.1,e.1], by linarith only [h.2,e.2]⟩
  · intro hs
    apply positiveGapPCC_iff_primeProbeTrace.mpr
    intro q hq
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hs q hq' (ε / 2) (by positivity)] with T ht
    rw [Real.dist_eq, sub_zero]
    exact (ht q ⟨hq', le_rfl⟩).trans_lt (by linarith)

/-- At any fixed width, bounds for three measured Cesàro traces imply a
pointwise gap estimate. The extra tolerance accounts for the proved drift of
the prime and smooth primitives and can be taken arbitrarily small. -/
theorem eventually_gap_error_of_three_signedCesaro {R h δ η : ℝ}
    (hh : 0 < h) (hR : h < R) (hη : 0 < η)
    (hl : ∀ᶠ T : ℝ in atTop, |cesaroSignedTrace T (R - h)| ≤ δ)
    (hm : ∀ᶠ T : ℝ in atTop, |cesaroSignedTrace T R| ≤ δ)
    (hu : ∀ᶠ T : ℝ in atTop, |cesaroSignedTrace T (R + h)| ≤ δ) :
    ∀ᶠ T : ℝ in atTop, |positiveGapMass T R - sineGapMass R| ≤
      h / 2 + (2 * R + h) * (δ + η) / (2 * h) := by
  have estimate (x : ℝ) (hx : 0 < x)
      (hb : ∀ᶠ T : ℝ in atTop, |cesaroSignedTrace T x| ≤ δ) :
      ∀ᶠ T : ℝ in atTop, |integratedGapDeficit T x| ≤ δ + η := by
    filter_upwards [Metric.tendsto_nhds.mp (cesaroSignedTrace_add_gapDeficit_fixed hx) η hη,
      hb] with T ht hT
    rw [Real.dist_eq, sub_zero] at ht
    have he := abs_lt.mp ht
    have hb' := abs_le.mp hT
    exact abs_le.mpr ⟨by linarith only [he.1, hb'.2], by linarith only [he.2, hb'.1]⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), estimate (R - h) (sub_pos.mpr hR) hl,
    estimate R (hh.trans hR) hm, estimate (R + h) (by linarith) hu] with T hT h₁ h₂ h₃
  exact gap_error_le_of_three_integrated_deficits hT hh hR h₁ h₂ h₃

end RiemannResearch.Analysis.MontgomeryPrimeTrace
