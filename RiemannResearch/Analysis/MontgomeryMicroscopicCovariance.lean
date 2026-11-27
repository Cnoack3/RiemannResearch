import RiemannResearch.Analysis.MontgomerySampledCountError

/-! # Strict pair correlation, the coincidence term and moving microscopic windows

Fujii's fixed-width moment bounds give bounded size. The identity below
retains the signed error in the covariance after subtracting the actual
equal-ordinate contribution. It characterizes the Dyson two-point limit on
all rational windows without a separate condition on horizontal multiplicity.
-/
noncomputable section
open Filter MeasureTheory Set intervalIntegral Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate

/-- The full same-ordinate term includes pairs of different labels at one height. -/
def strictWindowCovariance (T r : ℝ) : ℝ :=
  unfoldedWindowVariance T r - r * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))

/-- The off-diagonal covariance obtained by integrating the squared sine kernel. -/
def dysonWindowCovariance (r : ℝ) : ℝ :=
  -2 * ∫ u in (0 : ℝ)..r, (r-u) * Real.sinc (Real.pi*u)^2

theorem strictWindowCovariance_residual {r : ℝ} (hr : 0 < r) :
    ∀ᶠ T : ℝ in atTop, strictWindowCovariance T r - dysonWindowCovariance r =
      r^2 - unfoldedWindowMean T r ^ 2 - r * integratedGapDeficit T r := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_unfoldedWindowEnergy_eq_mean_sq_add_variance hr.le] with T hT hm
  have h := unfoldedWindowEnergy_sub_sine_eq_collision_sub_deficit hT hr
  rw [hm, sineWindowEnergy_eq] at h
  unfold strictWindowCovariance dysonWindowCovariance
  linarith only [h]

theorem strictWindowCovariance_tendsto_iff {r : ℝ} (hr : 0 < r) :
    Tendsto (fun T => strictWindowCovariance T r) atTop (𝓝 (dysonWindowCovariance r)) ↔
      Tendsto (fun T => integratedGapDeficit T r) atTop (𝓝 0) := by
  have hm := (unfoldedWindowMean_tendsto r).pow 2
  have hz : Tendsto (fun T => r^2 - unfoldedWindowMean T r ^ 2) atTop (𝓝 0) := by
    have hdiff : Tendsto (fun T => r^2 - unfoldedWindowMean T r ^ 2) atTop (𝓝 (r^2-r^2)) :=
      (tendsto_const_nhds (x := r^2)).sub hm
    rwa [sub_self] at hdiff
  have he := strictWindowCovariance_residual hr
  constructor
  · intro h
    have h' : Tendsto (fun T => strictWindowCovariance T r - dysonWindowCovariance r) atTop (𝓝 0) :=
      by simpa using h.sub_const (dysonWindowCovariance r)
    have hh := (hz.sub h').div_const r
    simp only [sub_zero, zero_div] at hh
    apply hh.congr'
    filter_upwards [he] with T hT
    rw [hT]
    field_simp [hr.ne']
    <;> ring
  · intro h
    have hh := (hz.sub (h.const_mul r)).add_const (dysonWindowCovariance r)
    simp only [mul_zero, sub_zero, zero_add] at hh
    apply hh.congr'
    filter_upwards [he] with T hT
    linarith only [hT]

theorem positiveGapPCC_iff_strictWindowCovariance :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun T : ℝ => strictWindowCovariance T q) atTop (𝓝 (dysonWindowCovariance q)) := by
  rw [positiveGapPCC_iff_rationalIntegratedGapDeficit]
  exact forall_congr' fun q => imp_congr_right fun hq =>
    (strictWindowCovariance_tendsto_iff (by exact_mod_cast hq : 0 < (q:ℝ))).symm

/-- The heights and widths can vary on any filter, including any increasing
sequence of heights. A positive finite limiting unfolded width suffices. -/
theorem PositiveGapPCC.moving_width {ι : Type*} {l : Filter ι} (h : PositiveGapPCC)
    {T R : ι → ℝ} {q : ℝ} (hT : Tendsto T l atTop) (hR : Tendsto R l (𝓝 q)) (hq : 0 < q) :
    Tendsto (fun i => positiveGapMass (T i) (R i)) l (𝓝 (sineGapMass q)) := by
  have hu : ∀ᶠ i in l, R i ∈ Icc (q/2) (q+1) :=
    ((hR.eventually (lt_mem_nhds (show q/2 < q by linarith))).and
      (hR.eventually (gt_mem_nhds (show q < q+1 by linarith)))).mono
      (fun _ hi => ⟨hi.1.le,hi.2.le⟩)
  have he : Tendsto (fun i => positiveGapMass (T i) (R i) - sineGapMass (R i)) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hu, hT.eventually (h (q/2) (q+1) (half_pos hq)
      (by linarith) (ε/2) (half_pos hε))] with i hi hh
    rw [Real.dist_eq, sub_zero]
    exact (hh _ hi).trans_lt (half_lt_self hε)
  have cs : Continuous sineGapMass := by
    apply continuous_primitive
    intro a b
    exact (show Continuous (fun u : ℝ => 1 - Real.sinc (Real.pi * u)^2) by fun_prop).intervalIntegrable a b
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using he.add ((cs.tendsto q).comp hR)

/-- Subtracting one common center changes none of the unfolded differences. -/
theorem recentered_gap (L t a b : ℝ) : L*(b-t) - L*(a-t) = L*(b-a) := by ring

end RiemannResearch.Analysis.MontgomeryPositiveGap
