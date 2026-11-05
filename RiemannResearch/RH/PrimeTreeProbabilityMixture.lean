/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeMellinLaws
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # The probability mixture on the log axis
Takashi Nakamura, Proc. Amer. Math. Soc. 143 (2015), 897–905, identifies
the limiting distribution. Here the finite-depth density and its translated
defect are the refinement described in Section 4.2 of *Prime trees, fractional
parts, and zeta zeros*. -/

noncomputable section
open MeasureTheory Set Filter
namespace RiemannResearch.RH.PrimeTreeMellinLaws

def logWeight (σ t : ℝ) : ℝ := Int.fract (Real.exp t) * Real.exp (-σ * t)
def logDepthWeight (D : ℕ) (σ t : ℝ) : ℝ := staircase D (Real.exp t) * Real.exp (-σ * t)
def missingMass (D : ℕ) (σ : ℝ) : ℝ := (D : ℝ) ^ (σ - 1)

def normalizedLaw (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (f t / ∫ u, f u))

private theorem logWeight_nonneg (σ t : ℝ) : 0 ≤ logWeight σ t :=
  mul_nonneg (Int.fract_nonneg _) (Real.exp_pos _).le

private theorem logDepthWeight_nonneg (D : ℕ) (σ t : ℝ) : 0 ≤ logDepthWeight D σ t :=
  mul_nonneg (staircase_nonneg _ _) (Real.exp_pos _).le

private theorem logWeight_measurable (σ : ℝ) : Measurable (logWeight σ) :=
  (measurable_fract.comp Real.measurable_exp).mul (by fun_prop)

theorem integrable_logWeight (σ : ℝ) (hσ : 0 < σ) (hσ' : σ < 1) : Integrable (logWeight σ) := by
  rw [← integrableOn_univ, ← (show Iic (0 : ℝ) ∪ Ioi 0 = univ from Iic_union_Ioi), integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic (sub_pos.mpr hσ') 0).mono'
      (logWeight_measurable σ).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t _
    rw [Real.norm_of_nonneg (logWeight_nonneg _ _)]
    have hfloor : (0 : ℝ) ≤ (⌊Real.exp t⌋ : ℝ) := by
      exact_mod_cast (Int.floor_nonneg.mpr (Real.exp_pos t).le)
    calc
      _ ≤ Real.exp t * Real.exp (-σ * t) :=
        mul_le_mul_of_nonneg_right (by unfold Int.fract; linarith) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hσ) 0).mono'
      (logWeight_measurable σ).aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_of_nonneg (logWeight_nonneg _ _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (Int.fract_lt_one _).le

theorem integral_logWeight_pos (σ : ℝ) (hσ : 0 < σ) (hσ' : σ < 1) :
    0 < ∫ t, logWeight σ t := by
  apply (integral_pos_iff_support_of_nonneg (logWeight_nonneg σ)
    (integrable_logWeight σ hσ hσ')).mpr
  have hsub : Ioo (-2 : ℝ) (-1) ⊆ Function.support (logWeight σ) := by
    intro t ht
    have ht0 : t < 0 := lt_trans ht.2 (by norm_num)
    have hf : Int.fract (Real.exp t) = Real.exp t :=
      Int.fract_eq_self.mpr ⟨(Real.exp_pos _).le, Real.exp_lt_one_iff.mpr ht0⟩
    change logWeight σ t ≠ 0
    rw [logWeight, hf]
    positivity
  exact lt_of_lt_of_le (by simp [Real.volume_Ioo]) (measure_mono hsub)

private theorem depth_le_limit (D : ℕ) (hD : 0 < D) (σ t : ℝ) :
    logDepthWeight D σ t ≤ logWeight σ t := by
  have h := (staircase_error D hD (Real.exp t) (Real.exp_pos _).le).1
  exact mul_le_mul_of_nonneg_right (sub_nonneg.mp h) (Real.exp_pos _).le

private theorem integrable_logDepthWeight (D : ℕ) (hD : 0 < D) (σ : ℝ)
    (hσ : 0 < σ) (hσ' : σ < 1) : Integrable (logDepthWeight D σ) := by
  have hstep : Measurable (fun t : ℝ => staircase D (Real.exp t)) :=
    (measurable_of_countable (Pareto.normalizedAtom D)).comp
      (Nat.measurable_floor.comp (measurable_const.mul Real.measurable_exp))
  apply (integrable_logWeight σ hσ hσ').mono' (hstep.mul (by fun_prop)).aestronglyMeasurable
  exact ae_of_all _ fun t => (Real.norm_of_nonneg (logDepthWeight_nonneg _ _ _)).trans_le
    (depth_le_limit D hD σ t)

/-- The exact correction is a copy of the entire logarithmic density translated
by minus the logarithm of the radix. -/
theorem logWeight_dilation (D : ℕ) (hD : 0 < D) (σ t : ℝ) :
    logWeight σ t = logDepthWeight D σ t + missingMass D σ * logWeight σ (t + Real.log D) := by
  have hd : 0 < (D : ℝ) := by exact_mod_cast hD
  have hfac : missingMass D σ * Real.exp (-σ * (t + Real.log D)) =
      Real.exp (-σ * t) / D := by
    rw [missingMass, Real.rpow_def_of_pos hd, ← Real.exp_add]
    calc
      _ = Real.exp (-σ * t - Real.log D) := congrArg Real.exp (by ring)
      _ = _ := by rw [Real.exp_sub, Real.exp_log hd]
  have hx : Real.exp (t + Real.log D) = (D : ℝ) * Real.exp t := by
    rw [Real.exp_add, Real.exp_log hd, mul_comm]
  rw [logWeight, logDepthWeight, staircase_eq_fract D hD _ (Real.exp_pos _).le,
    logWeight, hx, mul_left_comm, hfac]
  ring

private theorem missingMass_bounds (D : ℕ) (hD : 1 < D) (σ : ℝ) (hσ : σ < 1) :
    0 < missingMass D σ ∧ missingMass D σ < 1 := by
  have hd : (1 : ℝ) < D := by exact_mod_cast hD
  exact ⟨Real.rpow_pos_of_pos (zero_lt_one.trans hd) _,
    Real.rpow_lt_one_of_one_lt_of_neg hd (sub_neg.mpr hσ)⟩

private theorem integrable_defect (D : ℕ) (hD : 0 < D) (σ : ℝ)
    (hσ : 0 < σ) (hσ' : σ < 1) :
    Integrable (fun t : ℝ => missingMass D σ * logWeight σ (t + Real.log D)) := by
  apply ((integrable_logWeight σ hσ hσ').sub
    (integrable_logDepthWeight D hD σ hσ hσ')).congr
  apply ae_of_all
  intro t
  have h := logWeight_dilation D hD σ t
  change logWeight σ t - logDepthWeight D σ t = _
  linarith

/-- The exact normalizing mass at finite conductor. -/
theorem integral_logDepthWeight (D : ℕ) (hD : 0 < D) (σ : ℝ)
    (hσ : 0 < σ) (hσ' : σ < 1) :
    (∫ t, logDepthWeight D σ t) = (1 - missingMass D σ) * ∫ t, logWeight σ t := by
  have h := integral_congr_ae (μ := (volume : Measure ℝ))
    (ae_of_all _ (logWeight_dilation D hD σ))
  rw [integral_add (integrable_logDepthWeight D hD σ hσ hσ')
    (integrable_defect D hD σ hσ hσ'), integral_const_mul, integral_add_right_eq_self] at h
  linarith

private theorem normalizedLaw_apply {f : ℝ → ℝ} (hf : Integrable f) (hn : ∀ t, 0 ≤ f t)
    (hp : 0 < ∫ t, f t) {S : Set ℝ} (hS : MeasurableSet S) :
    normalizedLaw f S = ENNReal.ofReal ((∫ t in S, f t) / ∫ t, f t) := by
  rw [normalizedLaw, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn.div_const _)
      (ae_of_all _ fun t => div_nonneg (hn t) hp.le), integral_div]

theorem normalizedLaw_isProbability {f : ℝ → ℝ} (hf : Integrable f) (hn : ∀ t, 0 ≤ f t)
    (hp : 0 < ∫ t, f t) : IsProbabilityMeasure (normalizedLaw f) := by
  constructor
  rw [normalizedLaw_apply hf hn hp MeasurableSet.univ, setIntegral_univ, div_self hp.ne',
    ENNReal.ofReal_one]

private theorem normalizedLaw_real {f : ℝ → ℝ} (hf : Integrable f) (hn : ∀ t, 0 ≤ f t)
    (hp : 0 < ∫ t, f t) {S : Set ℝ} (hS : MeasurableSet S) :
    (normalizedLaw f).real S = (∫ t in S, f t) / ∫ t, f t := by
  rw [measureReal_def, normalizedLaw_apply hf hn hp hS,
    ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hn) hp.le)]

/-- Exact translated probability mixture, in the form of all measurable events. -/
theorem law_event_mixture (D : ℕ) (hD : 1 < D) (σ : ℝ) (hσ : 0 < σ) (hσ' : σ < 1)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (normalizedLaw (logWeight σ)).real S =
      (1 - missingMass D σ) * (normalizedLaw (logDepthWeight D σ)).real S +
      missingMass D σ * (normalizedLaw (logWeight σ)).real
        ((fun t : ℝ => t - Real.log D) ⁻¹' S) := by
  have hDp : 0 < D := by omega
  have hi := integrable_logWeight σ hσ hσ'
  have hdi := integrable_logDepthWeight D hDp σ hσ hσ'
  have hz := integral_logWeight_pos σ hσ hσ'
  have hδ := missingMass_bounds D hD σ hσ'
  have hmass := integral_logDepthWeight D hDp σ hσ hσ'
  have hden : 0 < ∫ t, logDepthWeight D σ t := by rw [hmass]; exact mul_pos (sub_pos.mpr hδ.2) hz
  have hT : MeasurableSet ((fun t : ℝ => t - Real.log D) ⁻¹' S) :=
    (measurable_id.sub measurable_const) hS
  have hshift : (∫ t in S, logWeight σ (t + Real.log D)) =
      ∫ t in ((fun u : ℝ => u - Real.log D) ⁻¹' S), logWeight σ t := by
    rw [← integral_indicator hS, ← integral_indicator hT]
    have hr := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (((fun u : ℝ => u - Real.log D) ⁻¹' S).indicator (logWeight σ)) (Real.log D)
    rw [← hr]
    apply integral_congr_ae
    filter_upwards with t
    have hpre : t + Real.log D ∈ (fun u : ℝ => u - Real.log D) ⁻¹' S ↔ t ∈ S := by
      change t + Real.log D - Real.log D ∈ S ↔ t ∈ S
      rw [add_sub_cancel_right]
    by_cases ht : t ∈ S
    · simp only [Set.indicator, if_pos ht, if_pos (hpre.mpr ht)]
    · simp only [Set.indicator, if_neg ht, if_neg (fun h => ht (hpre.mp h))]
  have h := integral_congr_ae (μ := (volume.restrict S)) (ae_of_all _ (logWeight_dilation D hDp σ))
  rw [integral_add hdi.integrableOn (integrable_defect D hDp σ hσ hσ').integrableOn,
    integral_const_mul, hshift] at h
  rw [normalizedLaw_real hi (logWeight_nonneg _) hz hS,
    normalizedLaw_real hdi (logDepthWeight_nonneg _ _) hden hS,
    normalizedLaw_real hi (logWeight_nonneg _) hz hT, hmass, h]
  field_simp [hz.ne', (sub_pos.mpr hδ.2).ne']
  <;> ring

/-- Equation (13) as the exact uniform-in-event estimate for total variation
with convention sup over measurable sets. -/
theorem law_event_totalVariation_bound (D : ℕ) (hD : 1 < D) (σ : ℝ) (hσ : 0 < σ)
    (hσ' : σ < 1) {S : Set ℝ} (hS : MeasurableSet S) :
    |(normalizedLaw (logDepthWeight D σ)).real S - (normalizedLaw (logWeight σ)).real S| ≤
      missingMass D σ := by
  have hd : 0 < D := by omega
  have hm := integral_logDepthWeight D hd σ hσ hσ'
  have hz := integral_logWeight_pos σ hσ hσ'
  have hδ := missingMass_bounds D hD σ hσ'
  letI := normalizedLaw_isProbability (integrable_logWeight σ hσ hσ') (logWeight_nonneg σ) hz
  letI := normalizedLaw_isProbability (integrable_logDepthWeight D hd σ hσ hσ')
    (logDepthWeight_nonneg D σ) (by rw [hm]; exact mul_pos (sub_pos.mpr hδ.2) hz)
  have h₁ : 0 ≤ (normalizedLaw (logDepthWeight D σ)).real S := measureReal_nonneg
  have h₂ : (normalizedLaw (logDepthWeight D σ)).real S ≤ 1 := measureReal_le_one
  have h₃ : 0 ≤ (normalizedLaw (logWeight σ)).real ((fun t : ℝ => t - Real.log D) ⁻¹' S) :=
    measureReal_nonneg
  have h₄ : (normalizedLaw (logWeight σ)).real ((fun t : ℝ => t - Real.log D) ⁻¹' S) ≤ 1 :=
    measureReal_le_one
  rw [law_event_mixture D hD σ hσ hσ' hS]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hδ.1.le h₁, mul_nonneg hδ.1.le (sub_nonneg.mpr h₄)]
  · nlinarith [mul_nonneg hδ.1.le h₃, mul_nonneg hδ.1.le (sub_nonneg.mpr h₂)]

end RiemannResearch.RH.PrimeTreeMellinLaws
