import RiemannResearch.RH.PrimeTreeNormalizedReadout
import RiemannResearch.RH.QAbsoluteChargeMass
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # The exponentially damped signed tree measure on the physical conductors

Source: Prime Trees, Carries and Zeta Zeros (5 November 2026), §7.3.
The measure is an integrable density with respect to counting measure.
Testing it against physical remainders gives actual convergent integrals.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeSubtreeBudget
open Pareto ZetaTwoHilbert

/-- Its mass at the conductor m; zero is included with zero weight. -/
def dampedChargeDensity (f : QHilbert) (t : ℝ) (m : ℕ) : ℝ :=
  charge f m / (m : ℝ) * Real.exp (-(t*(m:ℝ)))

/-- Finite total mass of the absolute values, including all conductors. -/
theorem dampedChargeDensity_summable_abs (f : QHilbert) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ => |dampedChargeDensity f t m|) := by
  have hb := (qSequence_mobiusDifference_absolute_mass f).mul_right (1/t)
  apply Summable.of_nonneg_of_le (fun m => abs_nonneg _) _ hb
  intro m
  by_cases hm : m = 0
  · simp [hm, dampedChargeDensity]
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hpow : (t * (m : ℝ)) ≤ Real.exp (t * (m : ℝ)) := by
    linarith [Real.add_one_le_exp (t * (m : ℝ))]
  have hkernel : (m : ℝ) * Real.exp (-(t*(m:ℝ))) ≤ 1/t := by
    apply (le_div_iff₀ ht).mpr
    rw [Real.exp_neg]
    calc
      _ = (t * (m : ℝ)) / Real.exp (t * (m : ℝ)) := by ring
      _ ≤ 1 := (div_le_one (Real.exp_pos _)).mpr hpow
  calc
    _ = (|charge f m| / (m : ℝ)^2) * ((m : ℝ) * Real.exp (-(t*(m:ℝ)))) := by
      rw [dampedChargeDensity, abs_mul, abs_div, abs_of_pos hm0, abs_of_pos (Real.exp_pos _)]
      field_simp [hm0.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hkernel (div_nonneg (abs_nonneg _) (sq_nonneg _))

theorem dampedChargeDensity_integrable (f : QHilbert) {t : ℝ} (ht : 0 < t) :
    Integrable (dampedChargeDensity f t) Measure.count := by
  apply integrable_count_iff.mpr
  simpa only [Real.norm_eq_abs] using (dampedChargeDensity_summable_abs f ht)

/-- The finite signed measure in equation (33). -/
def dampedChargeMeasure (f : QHilbert) (t : ℝ) : SignedMeasure ℕ :=
  Measure.count.withDensityᵥ (dampedChargeDensity f t)

theorem dampedChargeMeasure_singleton (f : QHilbert) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    dampedChargeMeasure f t {m} = dampedChargeDensity f t m := by
  rw [dampedChargeMeasure, withDensityᵥ_apply (dampedChargeDensity_integrable f ht)
    (measurableSet_singleton m), integral_singleton, count_real_singleton, one_smul]

/-- Nonnegative physical remainders are bounded by the physical site, even
when the conductor is larger than that site. -/
theorem dampedRemainder_integrable (f : QHilbert) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable (fun m : ℕ => ((n % m : ℕ) : ℝ) * dampedChargeDensity f t m)
      Measure.count := by
  apply integrable_count_iff.mpr
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _
    ((dampedChargeDensity_summable_abs f ht).mul_left (n : ℝ))
  intro m
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.mod_le n m) (abs_nonneg _)

/-- Writing the signed integral in its counting-density realization gives
the discrete series without an exchange of conditionally convergent sums. -/
theorem dampedRemainder_integral (f : QHilbert) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (∫ m : ℕ, ((n % m : ℕ) : ℝ) * dampedChargeDensity f t m ∂Measure.count) =
      ∑' k : ℕ, remainderTerm f n (k+1) * Real.exp (-(t*((k+1 : ℕ) : ℝ))) := by
  rw [integral_countable (dampedRemainder_integrable f ht n)]
  simp only [count_real_singleton, one_smul]
  have hs : Summable (fun m : ℕ => ((n % m : ℕ) : ℝ) * dampedChargeDensity f t m) :=
    (integrable_count_iff.mp (dampedRemainder_integrable f ht n)).of_norm
  rw [hs.tsum_eq_zero_add]
  simp only [dampedChargeDensity, Nat.cast_zero, div_zero, zero_mul, mul_zero, zero_add,
    remainderTerm, mul_assoc]

theorem dampedRemainder_integral_tendsto (f : QHilbert) (n : ℕ) :
    Tendsto (fun t : ℝ => ∫ m : ℕ, ((n % m : ℕ) : ℝ) * dampedChargeDensity f t m ∂Measure.count)
      (𝓝[>] 0) (𝓝 (-qSequence f n)) := by
  apply (physical_remainder_exponential_tendsto f n).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (dampedRemainder_integral f ht n).symm

/-- The strong integral limit, in the t↓0 parameter and the full Q norm. -/
theorem normalized_dampedIntegral_energy_tendsto (f : QHilbert) (a : ℝ) (ha : 1 / 2 < a) :
    Tendsto (fun t : ℝ => ∑' n : ℕ, positiveQWeight n *
      (((∫ m : ℕ, ((n % m : ℕ) : ℝ) * dampedChargeDensity f t m ∂Measure.count) +
        qSequence f n) / (n : ℝ)^a)^2) (𝓝[>] 0) (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  apply (((normalized_remainder_energy_tendsto f a ha).2).comp he).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply tsum_congr
  intro n
  rw [dampedRemainder_integral f ht n]
  have hexp (k : ℕ) : Real.exp (-t)^(k+1) = Real.exp (-(t*((k+1 : ℕ) : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [Function.comp_apply, hexp]

end RiemannResearch.RH.QPrimeSubtreeBudget
