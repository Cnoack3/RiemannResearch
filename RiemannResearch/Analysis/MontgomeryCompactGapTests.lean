import RiemannResearch.Analysis.MontgomerySmoothGapSandwich
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Integrating compact tests against the strictly positive ordinate gaps

A finite Stieltjes integration formula and dominated convergence upgrade
cumulative PCC to convergence for every continuously differentiable test
vanishing above a positive radius. -/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators ContDiff

namespace RiemannResearch.Analysis.MontgomeryAllPairWordRounding
open ActualZeroOrdinate MontgomeryPositiveGap

private def cutoffDerivative (d : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < d then (Ici d).indicator g x else 0

private lemma cutoffDerivative_integrable (d : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {g : ℝ → ℝ} (hg : Continuous g) :
    IntervalIntegrable (cutoffDerivative d g) volume 0 R := by
  by_cases hd : 0 < d
  · have he : cutoffDerivative d g = (Ici d).indicator g := by
      funext x
      simp only [cutoffDerivative, hd, if_true]
    rw [he, intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
    have hi : IntervalIntegrable g volume 0 R := hg.intervalIntegrable _ _
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp hi).indicator measurableSet_Ici
  · have he : cutoffDerivative d g = fun _ => 0 := by
      funext x
      simp only [cutoffDerivative, hd, if_false]
    rw [he]
    exact intervalIntegrable_const

private lemma integral_cutoffDerivative {f g : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (g x) x)
    (hg : Continuous g) {R : ℝ} (hR : 0 < R) (hz : ∀ x, R ≤ x → f x = 0) (d : ℝ) :
    (∫ x in (0 : ℝ)..R, cutoffDerivative d g x) = -(if 0 < d then f d else 0) := by
  by_cases hd₀ : 0 < d
  · simp only [cutoffDerivative, hd₀, if_true]
    have hi : Ici d ∩ Ioc 0 R = Icc d R := by
      ext x
      change (d ≤ x ∧ 0 < x ∧ x ≤ R) ↔ d ≤ x ∧ x ≤ R
      exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,hd₀.trans_le h.1,h.2⟩⟩
    rw [intervalIntegral.integral_of_le hR.le, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, hi]
    by_cases h : d ≤ R
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
          (hg.intervalIntegrable d R), hz R le_rfl, zero_sub]
    · rw [Icc_eq_empty_of_lt (lt_of_not_ge h), hz d (le_of_not_ge h)]
      simp
  · simp [cutoffDerivative, hd₀]

/-- Finite integration by parts, including arbitrarily close gaps and ties. -/
theorem actualPositiveTest_eq_neg_integral_cumulative {f g : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {T R : ℝ} (hT : 1 < T) (hR : 0 < R) (hz : ∀ x, R ≤ x → f x = 0) :
    actualPositiveTest T f = -(∫ x in (0 : ℝ)..R, positiveGapMass T x * g x) := by
  classical
  let L := Real.log T / (2*Real.pi)
  let D := T*Real.log T/(2*Real.pi)
  let d (i j : Copies T) := L*(copyOrdinate T j-copyOrdinate T i)
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have step (x : ℝ) : positiveGapMass T x * g x =
      (∑ i : Copies T, ∑ j : Copies T, cutoffDerivative (d i j) g x) / D := by
    change ((∑ i : Copies T, ∑ j : Copies T, if 0 < d i j ∧ d i j ≤ x then (1 : ℝ) else 0)/D)*g x = _
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : 0 < d i j <;> by_cases hx : d i j ≤ x <;>
      simp [cutoffDerivative, h, hx, Set.indicator, Set.mem_Ici]
  simp_rw [step]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_finsetSum
      (fun j _ => cutoffDerivative_integrable _ hR.le hg),
      integral_cutoffDerivative hd hg hR hz]
    simp only [Finset.sum_neg_distrib,neg_div,neg_neg]
    unfold actualPositiveTest positiveTestSum
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [d, mul_pos_iff_of_pos_left hL, sub_pos]
    rfl
  · intro i _
    apply intervalIntegrable_iff.mpr
    exact integrable_finsetSum _ (fun j _ => (cutoffDerivative_integrable (d i j) hR.le hg).def')

/-- Cumulative PCC gives the predicted integral for every compactly supported
C¹ test, and indeed only behavior on the positive half-line matters. -/
theorem actualPositiveTest_tendsto_of_positiveGapPCC {f g : ℝ → ℝ}
    (h : PositiveGapPCC) (hd : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {R : ℝ} (hR : 0 < R) (hz : ∀ x, R ≤ x → f x = 0) :
    Tendsto (fun T => actualPositiveTest T f) atTop
      (𝓝 (∫ x in (0 : ℝ)..R, f x * (1 - Real.sinc (Real.pi*x)^2))) := by
  let k (x : ℝ) := 1 - Real.sinc (Real.pi*x)^2
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hpoint (x : ℝ) (hx : 0 < x) : Tendsto (fun T => positiveGapMass T x)
      atTop (𝓝 (sineGapMass x)) := by
    apply Metric.tendsto_nhds.mpr
    intro e he
    filter_upwards [h x x hx le_rfl (e/2) (half_pos he)] with T hmass
    rw [Real.dist_eq]
    exact (hmass x ⟨le_rfl,le_rfl⟩).trans_lt (half_lt_self he)
  have hi : Tendsto (fun T => ∫ x in (0 : ℝ)..R, positiveGapMass T x * g x) atTop
      (𝓝 (∫ x in (0 : ℝ)..R, sineGapMass x * g x)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun x => (sineGapMass R + 1) * |g x|)
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
      exact ((positiveGapMass_mono hT).measurable.mul hg.measurable).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (1 : ℝ),
        (hpoint R hR).eventually_lt_const (lt_add_one _)] with T hT hB
      apply ae_of_all
      intro x hx
      rw [uIoc_of_le hR.le] at hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (positiveGapMass_nonneg hT x)]
      exact mul_le_mul_of_nonneg_right (((positiveGapMass_mono hT) hx.2).trans hB.le) (abs_nonneg _)
    · exact ((continuous_const.mul hg.abs).intervalIntegrable _ _)
    · apply ae_of_all
      intro x hx
      rw [uIoc_of_le hR.le] at hx
      exact (hpoint x hx.1).mul_const _
  have hder (x : ℝ) : HasDerivAt sineGapMass (k x) x := by
    exact intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 x)
      hk.stronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hmodel := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := R)
      (fun x _ => hder x) (fun x _ => hd x) (hk.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
  rw [hz R le_rfl, show sineGapMass 0 = 0 by simp [sineGapMass], mul_zero, zero_mul,
    sub_zero, zero_sub] at hmodel
  have htarget : -(∫ x in (0 : ℝ)..R, sineGapMass x * g x) =
      (∫ x in (0 : ℝ)..R, f x * k x) := by
    rw [hmodel,neg_neg]
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  have hcon := hi.neg
  rw [htarget] at hcon
  apply hcon.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact (actualPositiveTest_eq_neg_integral_cumulative hd hg hT hR hz).symm


/-- An exact smooth-test formulation of ordinary positive-gap PCC. The
radius is any positive cutoff outside which the test vanishes. -/
theorem positiveGapPCC_iff_even_compact_smooth_tests :
    PositiveGapPCC ↔ ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → (∀ x, f (-x) = f x) →
      ∀ R : ℝ, 0 < R → (∀ x, R ≤ |x| → f x = 0) →
      Tendsto (fun T => actualPositiveTest T f) atTop
        (𝓝 (∫ x in (0 : ℝ)..R, f x * (1 - Real.sinc (Real.pi * x)^2))) := by
  constructor
  · intro h f hf _ R hR hs
    apply actualPositiveTest_tendsto_of_positiveGapPCC h
      (fun x => (hf.differentiable (by simp) x).hasDerivAt)
      (hf.continuous_deriv (by simp)) hR
    intro x hx
    exact hs x (hx.trans (le_abs_self x))
  · intro h
    apply positiveGapPCC_of_even_bump_limits
    intro b
    apply h b b.contDiff b.neg b.rOut b.rOut_pos
    intro x hx
    exact b.zero_of_le_dist (by simpa [Real.dist_eq] using hx)

end RiemannResearch.Analysis.MontgomeryAllPairWordRounding
