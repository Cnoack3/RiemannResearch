import RiemannResearch.Analysis.FiniteWeightedVarianceCertificates
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact weight perturbations of finite means and variances

Source: independent finite weighted least-squares algebra.
The RH consumer is complete-weight occurrence certification. The movement of
the optimizer is retained as an exact squared remainder before estimation.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteWeightedVariance
variable {ι : Type*}

/-- Exact signed sensitivity of the weighted mean. -/
theorem mean_weight_perturbation (s : Finset ι) (w v f : ι → ℝ)
    (hW : mass s w ≠ 0) (hV : mass s v ≠ 0) :
    mass s v * (mean s v f - mean s w f) =
      ∑ i ∈ s, (v i - w i) * (f i - mean s w f) := by
  have he : (∑ i ∈ s, (v i - w i) * (f i - mean s w f)) =
      (∑ i ∈ s, v i * f i) - mass s v * mean s w f -
        (∑ i ∈ s, w i * f i) + mass s w * mean s w f := by
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    unfold mass
    ring
  rw [he, ← mass_mul_mean s v f hV, ← mass_mul_mean s w f hW]
  ring

/-- Exact weight perturbation, retaining the squared movement of the optimizer. -/
theorem variance_weight_perturbation (s : Finset ι) (w v f : ι → ℝ)
    (hV : mass s v ≠ 0) :
    variance s v f = variance s w f +
      (∑ i ∈ s, (v i - w i) * (f i - mean s w f)^2) -
        mass s v * (mean s v f - mean s w f)^2 := by
  have h := translation_energy s v f (-mean s w f) hV
  simp only [← sub_eq_add_neg] at h
  have he : (∑ i ∈ s, v i * (f i - mean s w f)^2) =
      variance s w f + ∑ i ∈ s, (v i - w i) * (f i - mean s w f)^2 := by
    simp only [variance, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he] at h
  linarith

theorem centered_abs_le_range (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < mass s w) (lo hi : ℝ)
    (hlo : ∀ i ∈ s, lo ≤ f i) (hhi : ∀ i ∈ s, f i ≤ hi)
    (i : ι) (hi' : i ∈ s) :
    |f i - mean s w f| ≤ hi - lo := by
  obtain ⟨hl,hu⟩ := mean_bounds s w f hw hW lo hi hlo hhi
  exact abs_le.mpr ⟨by linarith [hlo i hi'], by linarith [hhi i hi']⟩

/-- Total added weight gives an explicit mean error with the actual new mass denominator. -/
theorem mean_weight_error_le (s : Finset ι) (w v f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < mass s w)
    (hwv : ∀ i ∈ s, w i ≤ v i) (lo hi : ℝ)
    (hlo : ∀ i ∈ s, lo ≤ f i) (hhi : ∀ i ∈ s, f i ≤ hi) :
    |mean s v f - mean s w f| ≤
      (hi-lo) * mass s (fun i => v i - w i) / mass s v := by
  have hV : 0 < mass s v := hW.trans_le (Finset.sum_le_sum hwv)
  have h := congrArg abs (mean_weight_perturbation s w v f hW.ne' hV.ne')
  rw [abs_mul, abs_of_pos hV] at h
  apply (le_div_iff₀ hV).mpr
  calc
    _ = |∑ i ∈ s, (v i - w i) * (f i - mean s w f)| := by
      rw [mul_comm]
      exact h
    _ ≤ ∑ i ∈ s, |(v i - w i) * (f i - mean s w f)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (v i - w i) * (hi-lo) := by
      apply Finset.sum_le_sum
      intro i hi'
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hwv i hi'))]
      exact mul_le_mul_of_nonneg_left
        (centered_abs_le_range s w f hw hW lo hi hlo hhi i hi')
        (sub_nonneg.mpr (hwv i hi'))
    _ = _ := by rw [← Finset.sum_mul]; unfold mass; ring

/-- Explicit two-sided error in the optimized variance from increasing weights. -/
theorem variance_weight_error_bounds (s : Finset ι) (w v f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < mass s w)
    (hwv : ∀ i ∈ s, w i ≤ v i) (lo hi : ℝ)
    (hlo : ∀ i ∈ s, lo ≤ f i) (hhi : ∀ i ∈ s, f i ≤ hi) :
    0 ≤ variance s v f - variance s w f ∧
      variance s v f - variance s w f ≤
        (hi-lo)^2 * mass s (fun i => v i - w i) := by
  have hV : 0 < mass s v := hW.trans_le (Finset.sum_le_sum hwv)
  constructor
  · exact sub_nonneg.mpr (variance_le_of_weights s w v f hw hW.ne' hwv)
  · have he := variance_weight_perturbation s w v f hV.ne'
    have hb : (∑ i ∈ s, (v i - w i) * (f i - mean s w f)^2) ≤
        (hi-lo)^2 * mass s (fun i => v i - w i) := by
      calc
        _ ≤ ∑ i ∈ s, (v i - w i) * (hi-lo)^2 := by
          apply Finset.sum_le_sum
          intro i hi'
          apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hwv i hi'))
          have hh := centered_abs_le_range s w f hw hW lo hi hlo hhi i hi'
          have hrange : 0 ≤ hi-lo := (abs_nonneg _).trans hh
          nlinarith [sq_abs (f i - mean s w f),
            mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hrange (abs_nonneg (f i-mean s w f)))]
        _ = _ := by rw [← Finset.sum_mul]; unfold mass; ring
    nlinarith [mul_nonneg hV.le (sq_nonneg (mean s v f - mean s w f))]

end RiemannResearch.Analysis.FiniteWeightedVariance
