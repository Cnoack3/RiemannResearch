import RiemannResearch.Analysis.ZeroDPPPrimeVacancyPenalty
import RiemannResearch.Analysis.ZeroDPPVacancyDensity
import RiemannResearch.Analysis.ZeroDPPWidthAveragePCC

/-! The ordinary Montgomery conjecture and the zero-specific projected limit,
with their analytic upper and uniform-integrability providers quantified. -/
noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ZeroDPPProjectedCriterion
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryPositiveGap
open ProjectedDistinctSpacing ZeroDPPProjectionBridge ZeroDPPCollisionLoss
open ZeroDPPCorrelation ZeroDPPVacancyDensity DPPLargeWidth
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- A coarse consequence of the large-width GLSS bound for the actual count.
The height tends to infinity first, separately at each integer width. -/
def LargeWidthFullUpper : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
    (∫ r in (k:ℝ)..((k:ℝ)+1), unfoldedWindowEnergy T r) ≤
      (∫ r in (k:ℝ)..((k:ℝ)+1), sineWindowEnergy r) + η * (k:ℝ)^2

private theorem eventually_primeMissingDensity_bounds :
    ∀ᶠ T : ℝ in atTop, 0 ≤ primeMissingDensity T ∧ primeMissingDensity T ≤ 2 := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    tendsto_count_div_mainTerm.eventually (gt_mem_nhds (by norm_num : (1:ℝ) < 2))] with T ht hu
  have hx : 0 ≤ (Ncount 0 T : ℝ) - (actualOrdinateSupport T).card := by
    rw [← logarithmic_cutoff_vacancy]
    exact Finset.sum_nonneg fun i _ =>
      sub_nonneg.mpr ((limitingLaw_isDPP _).diagonal_bounds (liftCopy T i)).2
  have hd : 0 ≤ T * Real.log T / (2 * Real.pi) :=
    div_nonneg (mul_nonneg (zero_lt_one.trans ht).le (Real.log_pos ht).le) (by positivity)
  unfold primeMissingDensity
  refine ⟨div_nonneg hx hd, ?_⟩
  exact le_trans (div_le_div_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg _)) hd) hu.le

/-- The projected limit itself forces the normalized number of omitted
labels to vanish, once the full-count large-width upper estimate is supplied. -/
theorem primeMissingDensity_tendsto_of_projected (full : LargeWidthFullUpper)
    (proj : PrimeProjectedSineLimit) : Tendsto primeMissingDensity atTop (𝓝 0) := by
  apply vacancy_tendsto_of_cofinal_projected_lower primeMissingDensity
    (fun k T => ∫ r in (k:ℝ)..((k:ℝ)+1), unfoldedWindowEnergy T r)
    (fun k T => restoredPrimeMoment T (k:ℝ) ((k:ℝ)+1))
    (fun k => ∫ r in (k:ℝ)..((k:ℝ)+1), sineWindowEnergy r) 2 (by norm_num)
    eventually_primeMissingDensity_bounds prime_missing_density_penalty full
  intro η hη k₀
  let k := max k₀ 1
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hkr : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hq := proj (k:ℚ) ((k:ℚ)+1) (by exact_mod_cast hk) (by linarith)
  have hq' : Tendsto (fun T : ℝ => restoredPrimeMoment T (k:ℝ) ((k:ℝ)+1)) atTop
      (𝓝 (∫ r in (k:ℝ)..((k:ℝ)+1), sineWindowEnergy r)) := by simpa using hq
  refine ⟨k, le_max_left _ _, ?_⟩
  have hpos : 0 < η * (k:ℝ)^2 := mul_pos hη (sq_pos_of_pos hkr)
  exact (hq'.eventually (lt_mem_nhds (sub_lt_self _ hpos))).mono fun T hT => hT.le

private theorem simple_density_of_missing
    (hm : Tendsto primeMissingDensity atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  apply logarithmic_relativeVacancy_tendsto_zero_iff.mp
  have hd := hm.div tendsto_count_div_mainTerm (by norm_num : (1:ℝ) ≠ 0)
  rw [zero_div] at hd
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
  have ht' : 0 < T := zero_lt_one.trans ht
  have hden : T * Real.log T / (2 * Real.pi) ≠ 0 :=
    ne_of_gt (div_pos (mul_pos ht' (Real.log_pos ht)) (by positivity))
  change primeMissingDensity T / ((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) =
    cutoffVacancy _ T / (Ncount 0 T : ℝ)
  rw [logarithmic_cutoff_vacancy]
  unfold primeMissingDensity
  exact div_div_div_cancel_right₀ hden _ _

/-- Projection convergence implies the originally requested unweighted pair
loss on every positive rational interval under the two analytic providers. -/
theorem prime_loss_of_projected (full : LargeWidthFullUpper)
    (third : ∀ b : ℚ, 0 < b → BoundedTranslatedThirdMoment (b:ℝ))
    (proj : PrimeProjectedSineLimit) :
    ∀ a b : ℚ, 0 < a → a < b → Tendsto
      (fun T : ℝ => triangleLoss primeFrequencies T a b) atTop (𝓝 0) := by
  have hd := simple_density_of_missing (primeMissingDensity_tendsto_of_projected full proj)
  intro a b ha hab
  exact (prime_triangleLoss_tendsto_zero_iff (by exact_mod_cast ha : (0:ℝ)<(a:ℝ))
    (by exact_mod_cast hab : (a:ℝ)<(b:ℝ)) (third b (ha.trans hab))).mpr hd

theorem positiveGapPCC_of_primeProjectedSineLimit (full : LargeWidthFullUpper)
    (third : ∀ b : ℚ, 0 < b → BoundedTranslatedThirdMoment (b:ℝ))
    (proj : PrimeProjectedSineLimit) : PositiveGapPCC :=
  positiveGapPCC_of_prime_loss_and_restored (prime_loss_of_projected full third proj) proj

theorem primeProjectedSineLimit_of_positiveGapPCC (upper : ShortWindowSecondMomentUpper)
    (third : ∀ b : ℚ, 0 < b → BoundedTranslatedThirdMoment (b:ℝ))
    (hpcc : PositiveGapPCC) : PrimeProjectedSineLimit := by
  have hd := (density_one_of_positiveGapPCC hpcc upper).1
  have hs := sineWindowMoment_of_positiveGapPCC hpcc upper
  intro a b ha hab
  have ha' : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hab' : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
  have hl := (prime_triangleLoss_tendsto_zero_iff ha' hab' (third b (ha.trans hab))).mpr hd
  exact (restored_tendsto_iff_actual_of_loss hab'.le hl).mpr
    (integrated_window_energy_of_sine_moment hs ha' hab')

theorem primeProjectedSineLimit_iff_positiveGapPCC (full : LargeWidthFullUpper)
    (upper : ShortWindowSecondMomentUpper)
    (third : ∀ b : ℚ, 0 < b → BoundedTranslatedThirdMoment (b:ℝ)) :
    PrimeProjectedSineLimit ↔ PositiveGapPCC :=
  ⟨positiveGapPCC_of_primeProjectedSineLimit full third,
    primeProjectedSineLimit_of_positiveGapPCC upper third⟩

/--
info: 'RiemannResearch.Analysis.ZeroDPPProjectedCriterion.primeProjectedSineLimit_iff_positiveGapPCC'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProjectedSineLimit_iff_positiveGapPCC

end RiemannResearch.Analysis.ZeroDPPProjectedCriterion
