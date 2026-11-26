import RiemannResearch.Analysis.MicroscopicCountTail
import RiemannResearch.Analysis.ZeroDPPProjectionBridge

/-! The prime DPP deletes the excess of labels over the number of distinct
ordinates. Equal-height pairs alone give the sharp finite lower coefficient
from the microscopic Selberg trace note of November 25, 2026. -/
noncomputable section
open Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MicroscopicPrimeVacancy
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open ZeroDPPCollisionLoss ZeroDPPRankVacancy ZeroDPPProjectionBridge ProjectedDistinctSpacing
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

def primeDeletedFraction (T : ℝ) : ℝ :=
  ((Ncount 0 T : ℝ) - (actualOrdinateSupport T).card) / normalizer T

theorem primeVacancy_eq_deleted (T : ℝ) :
    cutoffVacancy primeFrequencies T / normalizer T = primeDeletedFraction T := by
  unfold primeDeletedFraction
  rw [← logarithmic_cutoff_vacancy]
  simp only [cutoffVacancy, primeFrequencies_limitingKernel, logarithmic_limitingKernel]

/-- A fiber of size m loses m(m−1) ordered pairs at zero and m−1 labels. -/
theorem twice_deleted_le_coincident (T : ℝ) :
    2 * ((Ncount 0 T : ℝ) - (actualOrdinateSupport T).card) ≤
      (occurrenceExcess (copyOrdinate T) : ℝ) := by
  have h := ZeroDPPCorrelation.twice_logarithmic_vacancy_add_count_le_collision T
  rw [logarithmic_cutoff_vacancy, actualCollision, occurrenceCollision_eq_card_add_excess,
    card_copies, Nat.cast_add] at h
  linarith

theorem prime_triangleLoss_lower {T a b : ℝ} (hT : 1 < T) (ha : 0 ≤ a) (hab : a ≤ b) :
    (b^2-a^2) * primeDeletedFraction T ≤ triangleLoss primeFrequencies T a b := by
  have hD : 0 < normalizer T :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have h := zero_lag_weight_le_triangleLoss primeFrequencies hT hab
  rw [integratedTriangle_eq_widthProbe hab, widthProbe_zero ha (ha.trans hab)] at h
  have hw : 0 ≤ (b^2-a^2)/2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hab) (add_nonneg (ha.trans hab) ha)]
  refine le_trans ?_ h
  have hh := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (twice_deleted_le_coincident T) hD.le) hw
  unfold primeDeletedFraction
  convert hh using 1 <;> ring

theorem eventually_prime_triangleLoss_log {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (he : MicroscopicCountTail.ExpTranslatedCountTail b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      0 ≤ primeDeletedFraction T → primeDeletedFraction T ≤ 1 →
        triangleLoss primeFrequencies T a b ≤
          C*primeDeletedFraction T*(1-Real.log (primeDeletedFraction T)) := by
  obtain ⟨C,hC,h⟩ := eventually_triangleLoss_logVacancy primeFrequencies ha hab
    (MicroscopicCountTail.expTranslatedSquareTail_of_exceedances he)
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T ht
  simpa only [primeVacancy_eq_deleted] using ht

end RiemannResearch.Analysis.MicroscopicPrimeVacancy
