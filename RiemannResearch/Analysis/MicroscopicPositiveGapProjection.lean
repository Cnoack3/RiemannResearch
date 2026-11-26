import RiemannResearch.Analysis.ZeroDPPProjectionBridge
import RiemannResearch.Analysis.ZeroDPPVacancyDensity
import RiemannResearch.Analysis.MontgomerySampledCountError

/-! The unweighted positive-gap statistic on the prime projection, its finite
multiplicity correction, and its comparison with the occurrence statistic. -/
noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MicroscopicPositiveGapProjection
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryPositiveGap
open ProjectedDistinctSpacing ZeroDPPCollisionLoss ZeroDPPVacancyDensity
open RiemannResearch.Probability.DPP RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

def gapIndicator (T q a b : ℝ) : ℝ :=
  let u := Real.log T / (2*Real.pi)*(b-a)
  if 0 < u ∧ u ≤ q then 1 else 0

def distinctPositiveMass (T q : ℝ) : ℝ :=
  distinctPairTest T (gapIndicator T q) / normalizer T

def multiplicityCorrection (T q : ℝ) : ℝ :=
  (∑ a ∈ actualOrdinateSupport T, ∑ b ∈ actualOrdinateSupport T,
     ((actualOrdinateMultiplicity T a : ℝ)*actualOrdinateMultiplicity T b-1) *
       gapIndicator T q a b) / normalizer T

private theorem gapIndicator_diag (T q a : ℝ) : gapIndicator T q a a = 0 := by
  simp [gapIndicator]

theorem positiveMass_eq_distinct_add_correction (T q : ℝ) :
    positiveGapMass T q = distinctPositiveMass T q + multiplicityCorrection T q := by
  let w := gapIndicator T q
  let m := fun u => (actualOrdinateMultiplicity T u : ℝ)
  let s := actualOrdinateSupport T
  let x := copyOrdinate T
  have hw : ∀ a b, (if a = b then 0 else w a b) = w a b := by
    intro a b
    by_cases he : a = b
    · subst b; simp [w,gapIndicator_diag]
    · simp [he]
  have he : (∑ i : Copies T, ∑ j : Copies T, w (x i) (x j)) =
      ∑ a ∈ s, ∑ b ∈ s, (m a * m b) * w a b := by
    have hi (a : ℝ) : (∑ j : Copies T, w a (x j)) = ∑ b ∈ s, m b * w a b :=
      sum_copies_by_ordinate T (w a)
    simp_rw [hi]
    rw [sum_copies_by_ordinate T (fun a => ∑ b ∈ s, m b * w a b)]
    simp only [Finset.mul_sum, mul_assoc, m, s]
  change (∑ i : Copies T, ∑ j : Copies T, w (x i) (x j)) / normalizer T =
    (∑ a ∈ s, ∑ b ∈ s, if a = b then 0 else w a b) / normalizer T +
    (∑ a ∈ s, ∑ b ∈ s, (m a * m b - 1) * w a b) / normalizer T
  rw [he, ← add_div]
  simp_rw [hw]
  congr 1
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro b _
  ring

theorem expected_prime_positive_eq_distinct (T q : ℝ) :
    expectedPairMass (limitingKernel primeFrequencies) (liftCopy T)
      (fun i j => gapIndicator T q (copyOrdinate T i) (copyOrdinate T j)) /
        normalizer T = distinctPositiveMass T q := by
  rw [prime_expectedPairMass_eq_distinct]; rfl

private theorem positiveIndicator_le_triangle (q u : ℝ) :
    (if 0 < u ∧ u ≤ q then (1:ℝ) else 0) ≤ integratedTriangle (q+1) (q+2) (-u) := by
  by_cases hu : 0 < u ∧ u ≤ q
  · rw [if_pos hu]
    have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : q+1 ≤ q+2)
      (f := fun _ : ℝ => 1) (g := fun r : ℝ => max (r-|-u|) 0)
      intervalIntegrable_const
      ((by fun_prop : Continuous (fun r : ℝ => max (r-|-u|) 0)).intervalIntegrable _ _)
      (fun r hr => (show 1 ≤ r-|-u| by rw [abs_neg,abs_of_pos hu.1]; linarith [hr.1,hu.2]).trans
        (le_max_left _ _))
    have hc : q+2-(q+1) = 1 := by ring
    simpa only [integratedTriangle,intervalIntegral.integral_const,smul_eq_mul,hc,one_mul] using h
  · rw [if_neg hu]
    exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => le_max_right _ _)

/-- The positive-gap multiplicity correction is nonnegative and the integrated
omission over a width interval one unit farther out dominates it. -/
theorem correction_sandwich {T : ℝ} (hT : 1 < T) (q : ℝ) :
    0 ≤ multiplicityCorrection T q ∧
      multiplicityCorrection T q ≤ triangleLoss primeFrequencies T (q+1) (q+2) := by
  classical
  let x := copyOrdinate T
  let L := Real.log T/(2*Real.pi)
  let w := fun i j : Copies T => gapIndicator T q (x i) (x j)
  let k := keptPair primeFrequencies T
  let K := limitingKernel primeFrequencies
  let e := liftCopy T
  have hD : 0 < normalizer T :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hk (i j : Copies T) : k i j ≤ 1 := calc
    _ ≤ (limitingLaw primeFrequencies).real univ :=
      measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    _ = 1 := by simp
  have hv (i j : Copies T) : 0 ≤ w i j := by dsimp [w,gapIndicator]; split_ifs <;> norm_num
  have hsum : (∑ i, ∑ j, w i j * k i j) = expectedPairMass K e w := by
    unfold expectedPairMass
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    by_cases he : i = j
    · subst j; simp [w,gapIndicator_diag]
    · have htwo := (limitingLaw_isDPP primeFrequencies).two_point (e.injective.ne he)
      change k i j = K (e i) (e i) * K (e j) (e j) - K (e i) (e j) * K (e j) (e i) at htwo
      rw [htwo]
  have he : multiplicityCorrection T q = (∑ i, ∑ j, w i j*(1-k i j))/normalizer T := by
    have hP := positiveMass_eq_distinct_add_correction T q
    rw [← expected_prime_positive_eq_distinct, ← hsum] at hP
    change (∑ i, ∑ j, w i j)/normalizer T = _ at hP
    have ha : (∑ i, ∑ j, w i j*(1-k i j))/normalizer T =
        (∑ i, ∑ j, w i j)/normalizer T - (∑ i, ∑ j, w i j*k i j)/normalizer T := by
      simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib,sub_div]
    rw [ha]; linarith
  rw [he]
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hv i j) (sub_nonneg.mpr (hk i j))) hD.le
  · unfold triangleLoss
    apply div_le_div_of_nonneg_right _ hD.le
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    by_cases hij : i = j
    · subst j; simp [w,gapIndicator_diag]
    · rw [if_neg hij]
      apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr (hk i j))
      change (if 0 < L*(x j-x i) ∧ L*(x j-x i) ≤ q then (1:ℝ) else 0) ≤
        integratedTriangle (q+1) (q+2) (L*(x i-x j))
      rw [show L*(x i-x j) = -(L*(x j-x i)) by ring]
      exact positiveIndicator_le_triangle _ _

theorem correction_tendsto_of_simpleDensity {q : ℝ} (hq : 0 < q)
    (h3 : BoundedTranslatedThirdMoment (q+2))
    (hd : Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun T : ℝ => multiplicityCorrection T q) atTop (𝓝 0) := by
  have hl := (prime_triangleLoss_tendsto_zero_iff (by linarith : 0 < q+1)
    (by linarith : q+1 < q+2) h3).mpr hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    exact (correction_sandwich ht q).1
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    exact (correction_sandwich ht q).2

theorem actual_tendsto_iff_distinct_of_correction {q g : ℝ}
    (h : Tendsto (fun T : ℝ => multiplicityCorrection T q) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => positiveGapMass T q) atTop (𝓝 g) ↔
      Tendsto (fun T : ℝ => distinctPositiveMass T q) atTop (𝓝 g) := by
  constructor
  · intro ha
    simpa only [positiveMass_eq_distinct_add_correction,add_sub_cancel_right,sub_zero] using ha.sub h
  · intro hd
    simpa only [positiveMass_eq_distinct_add_correction,add_zero] using hd.add h

/-- At fixed positive rational widths, simple-critical density and the exact
distinct-height law recover ordinary PCC. Its converse uses the established
short-window upper input that derives simple-critical density from PCC. -/
theorem positiveGapPCC_iff_density_and_distinct
    (hUpper : ShortWindowSecondMomentUpper)
    (h3 : ∀ q : ℚ, 0 < q → BoundedTranslatedThirdMoment ((q:ℝ)+2)) :
    PositiveGapPCC ↔
      (Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 1)) ∧
      ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ => distinctPositiveMass T q) atTop (𝓝 (sineGapMass q)) := by
  constructor
  · intro hp
    have hd := (density_one_of_positiveGapPCC hp hUpper).1
    refine ⟨hd, ?_⟩; intro q hq
    exact (actual_tendsto_iff_distinct_of_correction
      (correction_tendsto_of_simpleDensity (by exact_mod_cast hq) (h3 q hq) hd)).mp
        (positiveGapPCC_iff_rationalWidthLimits.mp hp q hq)
  · rintro ⟨hd, hh⟩
    apply positiveGapPCC_iff_rationalWidthLimits.mpr
    intro q hq
    exact (actual_tendsto_iff_distinct_of_correction
      (correction_tendsto_of_simpleDensity (by exact_mod_cast hq) (h3 q hq) hd)).mpr (hh q hq)

end RiemannResearch.Analysis.MicroscopicPositiveGapProjection
