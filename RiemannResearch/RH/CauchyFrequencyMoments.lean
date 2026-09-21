import RiemannResearch.RH.CriticalMellinMixtureEnergy
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Cauchy frequency measures: support and moment thresholds

Source: the user's Cauchy-frequency escape construction. The probability
measure is Mathlib's actual location-scale Cauchy law. Positive density gives
full support; comparison with Japanese brackets proves every fractional
absolute moment below one; comparison with the harmonic tail proves failure
of the first absolute moment. No transform or RH hypothesis enters.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

theorem volume_absolutelyContinuous_cauchyMeasure (γ : ℝ) (δ : ℝ≥0)
    (hδ : δ ≠ 0) : volume ≪ cauchyMeasure γ δ := by
  rw [cauchyMeasure_of_scale_ne_zero γ hδ]
  apply withDensity_absolutelyContinuous' (measurable_cauchyPDF γ δ).aemeasurable
  filter_upwards [] with t
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (cauchyPDF_pos γ hδ t))

/-- A positive-scale Cauchy frequency measure has no point atoms. -/
theorem cauchyMeasure_noAtoms (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) :
    NullSingletonClass (cauchyMeasure γ δ) := by
  rw [cauchyMeasure_of_scale_ne_zero γ hδ]
  infer_instance

/-- Every countable frequency set has zero Cauchy mass. -/
theorem cauchyMeasure_countable_null (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0)
    {S : Set ℝ} (hS : S.Countable) : cauchyMeasure γ δ S = 0 := by
  letI := cauchyMeasure_noAtoms γ δ hδ
  exact hS.measure_zero _

/-- The Cauchy escape cannot be a measure concentrated on countably many
frequencies. -/
theorem cauchyMeasure_not_ae_mem_countable (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0)
    {S : Set ℝ} (hS : S.Countable) :
    ¬ (∀ᵐ t ∂cauchyMeasure γ δ, t ∈ S) := by
  intro h
  have hSc : cauchyMeasure γ δ Sᶜ = 0 := h
  have hnull := measure_union_null (cauchyMeasure_countable_null γ δ hδ hS) hSc
  simpa only [Set.union_compl_self, measure_univ, one_ne_zero] using hnull

theorem cauchyMeasure_support_eq_univ (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) :
    (cauchyMeasure γ δ).support = Set.univ := by
  letI : (cauchyMeasure γ δ).IsOpenPosMeasure :=
    (volume_absolutelyContinuous_cauchyMeasure γ δ hδ).isOpenPosMeasure
  exact Measure.support_eq_univ

theorem cauchyMeasure_support_not_compact (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) :
    ¬ IsCompact (cauchyMeasure γ δ).support := by
  rw [cauchyMeasure_support_eq_univ γ δ hδ]
  exact noncompact_univ ℝ

/-- No finite frequency interval contains the measure almost everywhere. -/
theorem cauchyMeasure_not_ae_abs_le (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) (T : ℝ) :
    ¬ (∀ᵐ t ∂cauchyMeasure γ δ, |t| ≤ T) := by
  intro h
  have hs : (cauchyMeasure γ δ).support ⊆ Icc (-T) T :=
    Measure.support_subset_of_isClosed isClosed_Icc (by
      filter_upwards [h] with t ht
      exact abs_le.mp ht)
  rw [cauchyMeasure_support_eq_univ γ δ hδ] at hs
  have hb := hs (Set.mem_univ (T + 1))
  linarith [hb.2]

/-- Integrability is tested against the genuine positive Cauchy density. -/
theorem integrable_cauchyMeasure_iff (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0)
    (f : ℝ → ℝ) :
    Integrable f (cauchyMeasure γ δ) ↔
      Integrable (fun t => cauchyPDFReal γ δ t * f t) := by
  rw [cauchyMeasure_of_scale_ne_zero γ hδ,
    integrable_withDensity_iff_integrable_smul₀'
      (measurable_cauchyPDF γ δ).aemeasurable (by simp [cauchyPDF])]
  have heq : (fun t => (cauchyPDF γ δ t).toReal • f t) =
      (fun t => cauchyPDFReal γ δ t * f t) := by
    funext t
    rw [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos γ hδ t).le]
    rfl
  rw [heq]

private theorem abs_rpow_le_bracket (t α : ℝ) (hα : 0 ≤ α) :
    |t| ^ α ≤ (1 + t ^ 2) ^ (α / 2) := by
  calc
    _ = (t ^ 2) ^ (α / 2) := by
      rw [← sq_abs t, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg t)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow (sq_nonneg t) (by linarith) (by positivity)

private theorem cauchy_fractional_density_bound
    (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α t : ℝ), 0 ≤ α →
      cauchyPDFReal γ δ t * |t| ^ α ≤
        K * (1 + ‖t‖ ^ 2) ^ (-(2 - α) / 2) := by
  have hd : (0 : ℝ) < δ := by exact_mod_cast (pos_iff_ne_zero.mpr hδ)
  let C : ℝ := 2 + (1 + 2 * γ ^ 2) / (δ : ℝ) ^ 2
  let A : ℝ := Real.pi⁻¹ * (δ : ℝ)
  have hA : 0 < A := mul_pos (inv_pos.mpr Real.pi_pos) hd
  have hC2 : 2 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  have hC : 0 < C := by linarith
  have hCB : 1 + 2 * γ ^ 2 ≤ C * (δ : ℝ) ^ 2 := by
    dsimp [C]
    rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hd.ne')]
    nlinarith [sq_nonneg (δ : ℝ)]
  refine ⟨A * C, mul_pos hA hC, ?_⟩
  intro α t hα
  let D : ℝ := (t - γ) ^ 2 + (δ : ℝ) ^ 2
  let Q : ℝ := 1 + t ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hcomp : Q ≤ C * D := by
    have hm := mul_le_mul_of_nonneg_right hC2 (sq_nonneg (t - γ))
    dsimp [D, Q]
    nlinarith [sq_nonneg (t - 2 * γ)]
  have hpdf : cauchyPDFReal γ δ t ≤ A * C / Q := by
    change A * D⁻¹ ≤ _
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ hD hQ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcomp hA.le]
  have hp : |t| ^ α ≤ Q ^ (α / 2) := abs_rpow_le_bracket t α hα
  calc
    _ ≤ (A * C / Q) * Q ^ (α / 2) :=
      mul_le_mul hpdf hp (Real.rpow_nonneg (abs_nonneg t) α) (by positivity)
    _ = A * C * Q ^ (-(2 - α) / 2) := by
      rw [show -(2 - α) / 2 = α / 2 - 1 by ring,
        Real.rpow_sub hQ, Real.rpow_one]
      ring
    _ = _ := by simp [Q, Real.norm_eq_abs, sq_abs]

/-- All fractional absolute moments below the first moment are finite,
for arbitrary Cauchy location and positive scale. -/
theorem cauchyMeasure_integrable_abs_rpow (γ : ℝ) (δ : ℝ≥0)
    (hδ : δ ≠ 0) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Integrable (fun t : ℝ => |t| ^ α) (cauchyMeasure γ δ) := by
  rw [integrable_cauchyMeasure_iff γ δ hδ]
  obtain ⟨K, hK, hbound⟩ := cauchy_fractional_density_bound γ δ hδ
  have hbracket : Integrable (fun t : ℝ =>
      (1 + ‖t‖ ^ 2) ^ (-(2 - α) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using (show 1 < 2 - α by linarith))
  apply (hbracket.const_mul K).mono' (by fun_prop)
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (cauchyPDF_pos γ hδ t).le (Real.rpow_nonneg (abs_nonneg t) α))]
  exact hbound α t hα0

private theorem cauchy_first_density_lower (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 < t →
      B * t⁻¹ ≤ cauchyPDFReal γ δ t * |t| := by
  have hd : (0 : ℝ) < δ := by exact_mod_cast (pos_iff_ne_zero.mpr hδ)
  let A : ℝ := Real.pi⁻¹ * (δ : ℝ)
  let C : ℝ := 2 + 2 * γ ^ 2 + (δ : ℝ) ^ 2
  have hA : 0 < A := mul_pos (inv_pos.mpr Real.pi_pos) hd
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨A / (2 * C), div_pos hA (by positivity), ?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  let D : ℝ := (t - γ) ^ 2 + (δ : ℝ) ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hden : D ≤ 2 * C * t ^ 2 := by
    have ht2 : 1 ≤ t ^ 2 := by nlinarith
    have hsq : (t - γ) ^ 2 ≤ 2 * t ^ 2 + 2 * γ ^ 2 := by
      nlinarith [sq_nonneg (t + γ)]
    have hm := mul_le_mul_of_nonneg_left ht2
      (show 0 ≤ 2 * γ ^ 2 + (δ : ℝ) ^ 2 by positivity)
    have hmid : D ≤ C * t ^ 2 := by
      dsimp [D, C]
      nlinarith
    nlinarith [mul_nonneg hC.le (sq_nonneg t)]
  rw [abs_of_pos ht0]
  change A / (2 * C) * t⁻¹ ≤ A * D⁻¹ * t
  have hdiv : A / (2 * C * t ^ 2) ≤ A / D :=
    div_le_div_of_nonneg_left hA.le hD hden
  calc
    _ = (A / (2 * C * t ^ 2)) * t := by
      field_simp [ht0.ne', hC.ne']
    _ ≤ (A / D) * t := mul_le_mul_of_nonneg_right hdiv ht0.le
    _ = _ := by rw [div_eq_mul_inv]

/-- The first absolute Cauchy moment is infinite. -/
theorem cauchyMeasure_not_integrable_abs (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) :
    ¬ Integrable (fun t : ℝ => |t|) (cauchyMeasure γ δ) := by
  intro h
  have hp := (integrable_cauchyMeasure_iff γ δ hδ _).mp h
  obtain ⟨B, hB, hbound⟩ := cauchy_first_density_lower γ δ hδ
  have hi : IntegrableOn (fun t : ℝ => B * t⁻¹) (Ioi 1) := by
    apply hp.integrableOn.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hB (inv_pos.mpr (lt_trans zero_lt_one ht)))]
    exact hbound t ht
  have hir : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioi 1) := by
    have hh := hi.const_mul B⁻¹
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul,
      Real.rpow_neg_one] using hh
  have hf := (integrableOn_Ioi_rpow_iff zero_lt_one).mp hir
  linarith

/-- Constant-density Cauchy frequency mixtures fail the first-amplitude
moment hypothesis in the countable/finite-energy exclusion theorem. -/
theorem cauchyMeasure_not_integrable_criticalPoint_norm
    (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) :
    ¬ Integrable (fun t => ‖MellinFrequency.criticalPoint t‖) (cauchyMeasure γ δ) := by
  intro h
  apply cauchyMeasure_not_integrable_abs γ δ hδ
  apply h.mono' (by fun_prop)
  filter_upwards [] with t
  simpa [Real.norm_eq_abs, MellinFrequency.criticalPoint] using
    Complex.abs_im_le_norm (MellinFrequency.criticalPoint t)

end RiemannResearch.RH.Pareto.SpectralObstruction
