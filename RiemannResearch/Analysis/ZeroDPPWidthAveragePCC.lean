import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Width averaging in the converse direction for ordinary ordinate pair correlation.
The one-sided short-window hypothesis is the one in the existing PCC converse theorem.
Goldston, Lee, Schettler and Suriajaya, *Pair correlation conjecture for the zeros of
the Riemann zeta-function I*, Propositions 1 and 2, supply the analytic estimate on paper. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroWindowVariance

theorem integrated_window_energy_of_sine_moment (h : SineWindowMoment) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Tendsto (fun T : ℝ => ∫ r in a..b, unfoldedWindowEnergy T r) atTop
      (𝓝 (∫ r in a..b, sineWindowEnergy r)) := by
  have hB := (h b (ha.trans hab)).eventually
    (gt_mem_nhds (lt_add_one (sineWindowEnergy b)))
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => sineWindowEnergy b + 1)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact (unfoldedWindowEnergy_mono T hT).measurable.aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hB] with T hT hb
    apply ae_of_all
    intro r hr
    rw [uIoc_of_le hab.le] at hr
    have he : 0 ≤ unfoldedWindowEnergy T r := by
      unfold unfoldedWindowEnergy actualPhysicalTriangleEnergy
      apply div_nonneg _ (zero_lt_one.trans hT).le
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg he]
    exact ((unfoldedWindowEnergy_mono T hT) hr.2).trans hb.le
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro r hr
    rw [uIoc_of_le hab.le] at hr
    exact h r (ha.trans hr.1)

/-- Under the existing GLSS upper provider, the ordinary PCC is equivalent to the
actual signed width averages. This direction does not compare to a thinned measure. -/
theorem positiveGapPCC_iff_rationalTriangleWidthAverages (upper : ShortWindowSecondMomentUpper) :
    PositiveGapPCC ↔ RationalTriangleWidthAverages := by
  refine ⟨?_, positiveGapPCC_of_rationalTriangleWidthAverages⟩
  intro hp a b ha hab
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hc := integrated_window_energy_of_sine_moment
    (sineWindowMoment_of_positiveGapPCC hp upper) ha' hab'
  have hs := hc.sub_const (∫ r in (a : ℝ)..(b : ℝ), sineWindowEnergy r)
  rw [sub_self] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact (intervalIntegral.integral_sub (unfoldedWindowEnergy_mono T hT).intervalIntegrable
    (continuous_sineWindowEnergy.intervalIntegrable _ _)).symm
end RiemannResearch.Analysis.MontgomeryPositiveGap
