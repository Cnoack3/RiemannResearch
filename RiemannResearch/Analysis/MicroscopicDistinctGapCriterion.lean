import RiemannResearch.Analysis.MicroscopicPositiveGapProjection
import RiemannResearch.Analysis.MontgomeryGapTailDensity

/-! A one-sided count lower bound for actual occurrences follows from the
distinct-ordinate sine law. The GLSS short-window upper then forces essential
simplicity. This proves the reverse transfer without presupposing small vacancy. -/
noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.DistinctOrdinatePCC
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open MontgomeryPositiveGap MicroscopicPositiveGapProjection ZeroDPPVacancyDensity

def DistinctPositiveGapLaw : Prop :=
  ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ => distinctPositiveMass T q) atTop (𝓝 (sineGapMass q))

/-- Given the sine law on distinct zeta ordinates, ordinary PCC holds exactly
when the normalized excess from multiplicity weights vanishes at each positive
rational width. -/
theorem positiveGapPCC_iff_multiplicityCorrection_of_distinctLaw (hd : DistinctPositiveGapLaw) :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun T : ℝ => multiplicityCorrection T q) atTop (𝓝 0) := by
  constructor
  · intro hp q hq
    have ha := positiveGapPCC_iff_rationalWidthLimits.mp hp q hq
    simpa only [positiveMass_eq_distinct_add_correction, add_sub_cancel_left, sub_self] using
      ha.sub (hd q hq)
  · intro hc
    apply positiveGapPCC_iff_rationalWidthLimits.mpr
    intro q hq
    exact (actual_tendsto_iff_distinct_of_correction (hc q hq)).mpr (hd q hq)

/-- If every occupied height has one occurrence on all sufficiently large
cutoffs, the distinct-height sine law gives ordinary positive-gap PCC. -/
theorem positiveGapPCC_of_distinctLaw_of_singletonOrdinates (hd : DistinctPositiveGapLaw)
    (hm : ∀ᶠ T : ℝ in atTop, ∀ y ∈ actualOrdinateSupport T, actualOrdinateMultiplicity T y = 1) :
    PositiveGapPCC := by
  apply (positiveGapPCC_iff_multiplicityCorrection_of_distinctLaw hd).mpr
  intro q _
  apply tendsto_const_nhds.congr'
  filter_upwards [hm] with T hT
  symm
  unfold multiplicityCorrection
  have hz : (∑ a ∈ actualOrdinateSupport T, ∑ b ∈ actualOrdinateSupport T,
      ((actualOrdinateMultiplicity T a : ℝ) * actualOrdinateMultiplicity T b - 1) *
        gapIndicator T q a b) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    simp [hT a ha, hT b hb]
  rw [hz, zero_div]

/-- Density-one simple critical zeros with bounded translated third moments
also suffice to transfer the distinct-height law. -/
theorem positiveGapPCC_of_distinctLaw_of_simpleCriticalDensity (hd : DistinctPositiveGapLaw)
    (hs : Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1))
    (h3 : ∀ q : ℚ, 0 < q → BoundedTranslatedThirdMoment ((q : ℝ) + 2)) : PositiveGapPCC := by
  apply (positiveGapPCC_iff_multiplicityCorrection_of_distinctLaw hd).mpr
  intro q hq
  exact correction_tendsto_of_simpleDensity (by exact_mod_cast hq) (h3 q hq) hs

/-- info: 'RiemannResearch.Analysis.DistinctOrdinatePCC.positiveGapPCC_iff_multiplicityCorrection_of_distinctLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_multiplicityCorrection_of_distinctLaw

/-- info: 'RiemannResearch.Analysis.DistinctOrdinatePCC.positiveGapPCC_of_distinctLaw_of_singletonOrdinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_of_distinctLaw_of_singletonOrdinates

/-- info: 'RiemannResearch.Analysis.DistinctOrdinatePCC.positiveGapPCC_of_distinctLaw_of_simpleCriticalDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_of_distinctLaw_of_simpleCriticalDensity

/-- Rational widths need only exhibit the affine floor of the sine model. -/
def RationalDistinctAffineLower : Prop :=
  ∀ q : ℚ, 0 < q → ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop,
    (q:ℝ) - (1/2 + η) ≤ distinctPositiveMass T q

theorem rationalDistinctAffineLower_of_law (hs : DistinctPositiveGapLaw) :
    RationalDistinctAffineLower := by
  intro q hq η hη
  have hr : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  filter_upwards [(hs q hq).eventually_const_lt
    (by linarith : sineGapMass (q:ℝ) - η < sineGapMass (q:ℝ))] with T hT
  linarith only [hT, sineGapMass_lower hr.le]

private theorem affineFloor_of_distinct (hs : RationalDistinctAffineLower) {η : ℝ} (hη : 0 < η)
    (u : ℝ) (hu : 0 ≤ u) :
    ∀ᶠ T : ℝ in atTop, u - (1/2 + η) ≤ positiveGapMass T u := by
  by_cases hlo : u ≤ η
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    linarith only [positiveGapMass_nonneg hT u, hlo]
  · obtain ⟨r, hru, hur⟩ := exists_rat_btwn (by linarith : u-η/2 < u)
    have hr : (0:ℝ) < r := by linarith
    have hdist := hs r (by exact_mod_cast hr) (η/2) (half_pos hη)
    filter_upwards [hdist, eventually_gt_atTop (1:ℝ)] with T hQ hT
    have hcorr := (correction_sandwich hT (r:ℝ)).1
    have hmono := positiveGapMass_mono hT hur.le
    have he := positiveMass_eq_distinct_add_correction T (r:ℝ)
    linarith only [hru, hQ, hcorr, hmono, he]

/-- Only the lower side of the positive-spacing law enters the GLSS collision argument. -/
theorem collision_limit_of_rationalDistinctAffineLower
    (hs : RationalDistinctAffineLower) (hm : ShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T*Real.log T/(2*Real.pi)))
      atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [tendsto_count_div_mainTerm.eventually (lt_mem_nhds ha),
      eventually_gt_atTop (1:ℝ)] with T hN hT
    have hC : Ncount 0 T ≤ actualCollision T := by rw [actualCollision_eq_count_add_excess]; omega
    have hD : 0 ≤ T*Real.log T/(2*Real.pi) :=
      div_nonneg (mul_nonneg (zero_lt_one.trans hT).le (Real.log_pos hT).le) (by positivity)
    exact hN.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hC) hD)
  · intro b hb
    let η := (b-1)/8
    have hη : 0 < η := div_pos (sub_pos.mpr hb) (by norm_num)
    obtain ⟨R,hR,hupper⟩ := hm η hη
    have hR0 := zero_lt_one.trans_le hR
    have hl := eventually_integral_positiveGapMass_lower_of_affine (U:=0) (R:=R)
      (c:=1/2+η) hR0 hη (affineFloor_of_distinct hs hη)
    filter_upwards [hupper,hl,eventually_gt_atTop (1:ℝ)] with T hW hI hT
    rw [physicalTriangle_eq_collision_add_positive_gaps hT hR0.le] at hW
    let D := T*Real.log T/(2*Real.pi)
    change R*((actualCollision T : ℝ)/D) +
      2*(∫ u in (0:ℝ)..R, positiveGapMass T u) ≤ R^2+η*R at hW
    simp only [zero_pow (by decide : 2 ≠ 0),sub_zero] at hI
    have hle : R*((actualCollision T : ℝ)/D) ≤ R*(1+5*η) := by nlinarith only [hI,hW]
    exact (le_of_mul_le_mul_left hle hR0).trans_lt (by dsimp [η]; linarith)

theorem density_one_of_rationalDistinctAffineLower
    (hs : RationalDistinctAffineLower) (hm : ShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  (density_one_of_collision_limit (collision_limit_of_rationalDistinctAffineLower hs hm)).1

/-- Under the analytic short-window upper and translated fixed third moments,
the positive cumulative law on the deterministically reduced support is
equivalent to ordinary PCC. -/
theorem positiveGapPCC_iff_distinctPositiveGapLaw
    (hm : ShortWindowSecondMomentUpper)
    (h3 : ∀ q : ℚ, 0 < q → BoundedTranslatedThirdMoment ((q:ℝ)+2)) :
    PositiveGapPCC ↔ DistinctPositiveGapLaw := by
  constructor
  · intro hp
    exact ((positiveGapPCC_iff_density_and_distinct hm h3).mp hp).2
  · intro hs
    exact (positiveGapPCC_iff_density_and_distinct hm h3).mpr
      ⟨density_one_of_rationalDistinctAffineLower (rationalDistinctAffineLower_of_law hs) hm, hs⟩

end RiemannResearch.Analysis.DistinctOrdinatePCC
