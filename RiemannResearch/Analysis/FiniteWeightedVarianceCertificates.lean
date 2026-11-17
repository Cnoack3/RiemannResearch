import RiemannResearch.Analysis.FiniteWeightedVariance
import Mathlib.Tactic.NormNum

/-!
# Exact variance remainders and certified weighted means

Source: independent finite algebra built from `FiniteWeightedVariance`.
The concrete RH consumer is the complete-weight occurrence optimizer.
All identities retain their signed remainder. Weight enclosures certify the
actual optimizer, including its dependence on the weights; no floating-point
value or asymptotic estimate is assumed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteWeightedVariance
variable {ι : Type*}

theorem mass_mul_mean (s : Finset ι) (w f : ι → ℝ) (hW : mass s w ≠ 0) :
    mass s w * mean s w f = ∑ i ∈ s, w i * f i := by
  exact mul_div_cancel₀ _ hW

theorem mean_sub_eq (s : Finset ι) (w f : ι → ℝ) (hW : mass s w ≠ 0) (z : ℝ) :
    mean s w f - z = (∑ i ∈ s, w i * (f i - z)) / mass s w := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change mean s w f - z = ((∑ i ∈ s, w i * f i) - mass s w * z) / mass s w
  rw [sub_div, mul_div_cancel_left₀ z hW]
  rfl

theorem le_mean_iff_centered_sum_nonneg (s : Finset ι) (w f : ι → ℝ)
    (hW : 0 < mass s w) (z : ℝ) :
    z ≤ mean s w f ↔ 0 ≤ ∑ i ∈ s, w i * (f i - z) := by
  rw [← sub_nonneg, mean_sub_eq s w f hW.ne' z]
  rw [le_div_iff₀ hW, zero_mul]

theorem mean_le_iff_centered_sum_nonpos (s : Finset ι) (w f : ι → ℝ)
    (hW : 0 < mass s w) (z : ℝ) :
    mean s w f ≤ z ↔ (∑ i ∈ s, w i * (f i - z)) ≤ 0 := by
  rw [← sub_nonpos, mean_sub_eq s w f hW.ne' z]
  rw [div_le_iff₀ hW, zero_mul]

theorem mean_bounds (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < mass s w) (lo hi : ℝ)
    (hlo : ∀ i ∈ s, lo ≤ f i) (hhi : ∀ i ∈ s, f i ≤ hi) :
    lo ≤ mean s w f ∧ mean s w f ≤ hi := by
  constructor
  · apply (le_mean_iff_centered_sum_nonneg s w f hW lo).mpr
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sub_nonneg.mpr (hlo i hi)))
  · apply (mean_le_iff_centered_sum_nonpos s w f hW hi).mpr
    exact Finset.sum_nonpos (fun i hi => mul_nonpos_of_nonneg_of_nonpos (hw i hi)
      (sub_nonpos.mpr (hhi i hi)))

theorem variance_eq_trial_sub_defect (s : Finset ι) (w f : ι → ℝ)
    (hW : mass s w ≠ 0) (z : ℝ) :
    variance s w f = (∑ i ∈ s, w i * (f i - z) ^ 2) -
      (∑ i ∈ s, w i * (f i - z)) ^ 2 / mass s w := by
  have ht := translation_energy s w f (-z) hW
  have hm := mean_sub_eq s w f hW z
  simp only [← sub_eq_add_neg] at ht
  rw [hm] at ht
  have he : mass s w * ((∑ i ∈ s, w i * (f i - z)) / mass s w) ^ 2 =
      (∑ i ∈ s, w i * (f i - z)) ^ 2 / mass s w := by
    field_simp
  rw [he] at ht
  linarith

theorem variance_endpoint_identity (s : Finset ι) (w f : ι → ℝ)
    (hW : mass s w ≠ 0) (lo hi : ℝ) :
    variance s w f + (∑ i ∈ s, w i * (hi - f i) * (f i - lo)) =
      mass s w * (hi - mean s w f) * (mean s w f - lo) := by
  have hm := mass_mul_mean s w f hW
  have ht := translation_energy s w f 0 hW
  simp only [add_zero] at ht
  have he : (∑ i ∈ s, w i * (hi - f i) * (f i - lo)) =
      (hi + lo) * (∑ i ∈ s, w i * f i) -
        (∑ i ∈ s, w i * f i ^ 2) - hi * lo * mass s w := by
    unfold mass
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, ← hm]
  nlinarith only [ht]

theorem variance_le_mean_endpoints (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : mass s w ≠ 0) (lo hi : ℝ)
    (hlo : ∀ i ∈ s, lo ≤ f i) (hhi : ∀ i ∈ s, f i ≤ hi) :
    variance s w f ≤ mass s w * (hi - mean s w f) * (mean s w f - lo) := by
  rw [← variance_endpoint_identity s w f hW lo hi]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i hi =>
    mul_nonneg (mul_nonneg (hw i hi) (sub_nonneg.mpr (hhi i hi)))
      (sub_nonneg.mpr (hlo i hi))))

theorem mean_endpoints_le_quarter_range (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (lo hi : ℝ) :
    mass s w * (hi - mean s w f) * (mean s w f - lo) ≤
      mass s w * (hi - lo) ^ 2 / 4 := by
  have h := mul_nonneg (show 0 ≤ mass s w from Finset.sum_nonneg hw)
    (sq_nonneg (mean s w f - (lo + hi) / 2))
  nlinarith

theorem variance_eq_zero_iff (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    variance s w f = 0 ↔ ∀ i ∈ s, f i = mean s w f := by
  constructor
  · intro h i hi
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => mul_nonneg (hw j hj).le (sq_nonneg (f j - mean s w f)))).mp h i hi
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (hw i hi).ne'))
  · intro h
    exact Finset.sum_eq_zero (fun i hi => by rw [h i hi, sub_self, zero_pow (by decide), mul_zero])


/-- Interval multiplication with a signed second factor.
The weight endpoints need not be positive. -/
theorem min_mul_le_of_bounds {a b w z : ℝ} (ha : a ≤ w) (hb : w ≤ b) :
    min (a * z) (b * z) ≤ w * z := by
  by_cases hz : 0 ≤ z
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right ha hz)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hb (le_of_not_ge hz))

theorem mul_le_max_of_bounds {a b w z : ℝ} (ha : a ≤ w) (hb : w ≤ b) :
    w * z ≤ max (a * z) (b * z) := by
  by_cases hz : 0 ≤ z
  · exact (mul_le_mul_of_nonneg_right hb hz).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right ha (le_of_not_ge hz)).trans (le_max_left _ _)

/-- Certified signs of centered sums enclose the true weighted mean without dividing intervals. -/
theorem mean_enclosure_of_weight_bounds (s : Finset ι) (w f lower upper : ι → ℝ)
    (hW : 0 < mass s w) (hw : ∀ i ∈ s, lower i ≤ w i ∧ w i ≤ upper i)
    (lo hi : ℝ)
    (hlo : 0 ≤ ∑ i ∈ s, min (lower i * (f i - lo)) (upper i * (f i - lo)))
    (hhi : (∑ i ∈ s, max (lower i * (f i - hi)) (upper i * (f i - hi))) ≤ 0) :
    lo ≤ mean s w f ∧ mean s w f ≤ hi := by
  constructor
  · apply (le_mean_iff_centered_sum_nonneg s w f hW lo).mpr
    exact hlo.trans (Finset.sum_le_sum (fun i hi =>
      min_mul_le_of_bounds (hw i hi).1 (hw i hi).2))
  · apply (mean_le_iff_centered_sum_nonpos s w f hW hi).mpr
    exact (Finset.sum_le_sum (fun i hi =>
      mul_le_max_of_bounds (hw i hi).1 (hw i hi).2)).trans hhi

/-- A residual enclosure yields a quantitative error certificate for an approximate mean. -/
theorem mean_error_sq_le (s : Finset ι) (w f : ι → ℝ)
    (hW : 0 < mass s w) (z e : ℝ)
    (hres : (∑ i ∈ s, w i * (f i - z)) ^ 2 ≤ e ^ 2 * mass s w ^ 2) :
    (mean s w f - z) ^ 2 ≤ e ^ 2 := by
  rw [mean_sub_eq s w f hW.ne' z, div_pow]
  exact (div_le_iff₀ (sq_pos_of_pos hW)).mpr hres

/-- Weight intervals bound the optimized variance itself, including the change in optimizer. -/
theorem variance_enclosure_of_weight_bounds (s : Finset ι) (w f lower upper : ι → ℝ)
    (hlower : ∀ i ∈ s, 0 ≤ lower i) (hL : 0 < mass s lower)
    (hw : ∀ i ∈ s, lower i ≤ w i ∧ w i ≤ upper i) :
    variance s lower f ≤ variance s w f ∧ variance s w f ≤ variance s upper f := by
  have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hlower i hi).trans (hw i hi).1
  have hW : 0 < mass s w := hL.trans_le (Finset.sum_le_sum (fun i hi => (hw i hi).1))
  exact ⟨variance_le_of_weights s lower w f hlower hL.ne' (fun i hi => (hw i hi).1),
    variance_le_of_weights s w upper f hw0 hW.ne' (fun i hi => (hw i hi).2)⟩

end RiemannResearch.Analysis.FiniteWeightedVariance
