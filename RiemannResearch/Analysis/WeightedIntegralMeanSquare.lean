/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Mean-square transfer through an integrable envelope

Weighted Cauchy--Schwarz and Fubini transfer uniform square moments through
a full real-line integral. A bounded continuous family and a nonnegative
continuous L1 envelope give the required product integrability. The
complex integral and its squared norm are also proved interval integrable.

The intended consumer is the transformed Mellin remainder for the actual
zeta square: Gamma supplies the L1 envelope and translated divisor
polynomials or tails supply the family of moments.

Source: standard weighted Cauchy--Schwarz and Fubini, formalized from
Mathlib's integral Holder inequality and product-integral theorem.
-/
noncomputable section
open MeasureTheory Set
namespace MeasureTheory

/-- Weighted Cauchy--Schwarz for a dominated complex integral over the whole line. -/
theorem norm_integral_sq_le_weighted_continuous
    {k : ℝ → ℝ} {F G : ℝ → ℂ} (hk : Continuous k)
    (hki : Integrable k) (hk0 : ∀ v, 0 ≤ k v)
    (hF : Continuous F) (hG : Continuous G)
    {D : ℝ} (hFb : ∀ v, ‖F v‖ ≤ D)
    (hGb : ∀ v, ‖G v‖ ≤ k v * ‖F v‖) :
    ‖∫ v : ℝ, G v‖ ^ 2 ≤
      (∫ v : ℝ, k v) * (∫ v : ℝ, k v * ‖F v‖ ^ 2) := by
  have hFint : Integrable (fun v => k v * ‖F v‖) :=
    (hki.mul_const D).mono' (hk.mul hF.norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 v) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hFb v) (hk0 v))
  have hF2int : Integrable (fun v => k v * ‖F v‖ ^ 2) :=
    (hki.mul_const (D ^ 2)).mono' (hk.mul (hF.norm.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 v) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hFb v) 2) (hk0 v))
  have hGi : Integrable G :=
    hFint.mono' hG.aestronglyMeasurable (Filter.Eventually.of_forall hGb)
  have hL1 : MemLp (fun v => Real.sqrt (k v)) (ENNReal.ofReal 2) volume := by
    apply (integrable_norm_rpow_iff hk.sqrt.aestronglyMeasurable
      (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hk0 _)] using hki
  have hL2 : MemLp (fun v => Real.sqrt (k v) * ‖F v‖)
      (ENNReal.ofReal 2) volume := by
    apply (integrable_norm_rpow_iff (hk.sqrt.mul hF.norm).aestronglyMeasurable
      (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2),
      Pi.mul_apply, Real.rpow_two, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt (hk0 _)] using hF2int
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
    (f := fun v => Real.sqrt (k v)) (g := fun v => Real.sqrt (k v) * ‖F v‖)
    (Filter.Eventually.of_forall fun v => Real.sqrt_nonneg _)
    (Filter.Eventually.of_forall fun v => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    hL1 hL2
  have he (v : ℝ) : Real.sqrt (k v) * (Real.sqrt (k v) * ‖F v‖) =
      k v * ‖F v‖ := by rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hk0 v)]
  have hcs' : (∫ v : ℝ, k v * ‖F v‖) ≤
      Real.sqrt (∫ v : ℝ, k v) * Real.sqrt (∫ v : ℝ, k v * ‖F v‖ ^ 2) := by
    simpa only [he, Real.rpow_two, mul_pow, Real.sq_sqrt (hk0 _),
      ← Real.sqrt_eq_rpow] using hcs
  have hnorm : ‖∫ v : ℝ, G v‖ ≤ ∫ v : ℝ, k v * ‖F v‖ :=
    (norm_integral_le_integral_norm G).trans
      (integral_mono_ae hGi.norm hFint (Filter.Eventually.of_forall hGb))
  have hkn : 0 ≤ ∫ v : ℝ, k v := integral_nonneg hk0
  have hFn : 0 ≤ ∫ v : ℝ, k v * ‖F v‖ ^ 2 :=
    integral_nonneg fun v => mul_nonneg (hk0 v) (sq_nonneg _)
  have hp := pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hcs') 2
  simpa only [mul_pow, Real.sq_sqrt hkn, Real.sq_sqrt hFn] using hp


/-- The full inner integral and its square norm are integrable on each
finite outer interval when dominated there by an L1 envelope. -/
theorem intervalIntegrable_integral_and_norm_sq_of_weighted_bound
    {k : ℝ → ℝ} {G : ℝ × ℝ → ℂ}
    (hki : Integrable k) (hG : Continuous G)
    {D H T : ℝ} (hHT : H ≤ T)
    (hGb : ∀ t ∈ Icc H T, ∀ v, ‖G (t, v)‖ ≤ k v * D) :
    IntervalIntegrable (fun t => ∫ v : ℝ, G (t, v)) volume H T ∧
      IntervalIntegrable (fun t => ‖∫ v : ℝ, G (t, v)‖ ^ 2) volume H T := by
  let μ : Measure ℝ := volume.restrict (Ioc H T)
  have hmeas : StronglyMeasurable (fun t : ℝ => ∫ v : ℝ, G (t, v)) :=
    (show StronglyMeasurable (Function.uncurry (fun t v => G (t, v))) from
      hG.stronglyMeasurable).integral_prod_right
  have hpoint : ∀ t ∈ Icc H T, ‖∫ v : ℝ, G (t, v)‖ ≤ (∫ v : ℝ, k v) * D := by
    intro t ht
    have hc : Continuous (fun v : ℝ => G (t, v)) :=
      hG.comp (continuous_const.prodMk continuous_id)
    have hi : Integrable (fun v : ℝ => G (t, v)) :=
      (hki.mul_const D).mono' hc.aestronglyMeasurable
        (Filter.Eventually.of_forall (hGb t ht))
    calc
      _ ≤ ∫ v : ℝ, ‖G (t, v)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, k v * D :=
        integral_mono_ae hi.norm (hki.mul_const D)
          (Filter.Eventually.of_forall (hGb t ht))
      _ = _ := integral_mul_const D k
  have hi : Integrable (fun t : ℝ => ∫ v : ℝ, G (t, v)) μ := by
    apply (integrable_const ((∫ v : ℝ, k v) * D)).mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpoint t ⟨ht.1.le, ht.2⟩
  have hi2 : Integrable (fun t : ℝ => ‖∫ v : ℝ, G (t, v)‖ ^ 2) μ := by
    apply (integrable_const (((∫ v : ℝ, k v) * D) ^ 2)).mono'
      (hmeas.norm.pow 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hpoint t ⟨ht.1.le, ht.2⟩) 2
  have hempty : Ioc T H = (∅ : Set ℝ) := Ioc_eq_empty_of_le hHT
  constructor
  · constructor
    · exact hi
    · rw [hempty]
      exact integrableOn_empty
  · constructor
    · exact hi2
    · rw [hempty]
      exact integrableOn_empty

/-- A nonnegative integrable envelope transfers a uniform family of interval
square moments through a full real-line integral. The envelope bound is
required only on the outer interval. -/
theorem interval_integral_norm_integral_sq_le_weighted
    {k : ℝ → ℝ} {F G : ℝ × ℝ → ℂ} (hk : Continuous k)
    (hki : Integrable k) (hk0 : ∀ v, 0 ≤ k v)
    (hF : Continuous F) (hG : Continuous G)
    {D M H T : ℝ} (hHT : H ≤ T) (hFb : ∀ p, ‖F p‖ ≤ D)
    (hGb : ∀ t ∈ Icc H T, ∀ v, ‖G (t, v)‖ ≤ k v * ‖F (t, v)‖)
    (hM : ∀ v, (∫ t in H..T, ‖F (t, v)‖ ^ 2) ≤ M) :
    (∫ t in H..T, ‖∫ v : ℝ, G (t, v)‖ ^ 2) ≤
      (∫ v : ℝ, k v) ^ 2 * M := by
  let μ : Measure ℝ := volume.restrict (Ioc H T)
  let W : ℝ × ℝ → ℝ := fun p => k p.2 * ‖F p‖ ^ 2
  have hWc : Continuous W := (hk.comp continuous_snd).mul (hF.norm.pow 2)
  have hWi : Integrable W (μ.prod volume) := by
    apply ((integrable_const (D ^ 2) : Integrable (fun _ : ℝ => D ^ 2) μ).mul_prod hki).mono'
      hWc.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro p
    dsimp [W]
    rw [abs_of_nonneg (mul_nonneg (hk0 p.2) (sq_nonneg _))]
    calc
      _ ≤ k p.2 * D ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hFb p) 2) (hk0 p.2)
      _ = _ := mul_comm _ _
  have hkint : 0 ≤ ∫ v : ℝ, k v := integral_nonneg hk0
  have hpoint : ∀ t ∈ Icc H T,
      ‖∫ v : ℝ, G (t, v)‖ ^ 2 ≤ (∫ v : ℝ, k v) *
        ∫ v : ℝ, W (t, v) := by
    intro t ht
    exact norm_integral_sq_le_weighted_continuous hk hki hk0
      (hF.comp (continuous_const.prodMk continuous_id))
      (hG.comp (continuous_const.prodMk continuous_id))
      (fun v => hFb (t, v)) (hGb t ht)
  have hfirst : (∫ t, ‖∫ v : ℝ, G (t, v)‖ ^ 2 ∂μ) ≤
      (∫ v : ℝ, k v) * (∫ t, (∫ v : ℝ, W (t, v)) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (hWi.integral_prod_left.const_mul (∫ v : ℝ, k v))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpoint t ⟨ht.1.le, ht.2⟩
  have hswap : (∫ t, (∫ v : ℝ, W (t, v)) ∂μ) =
      ∫ v : ℝ, ∫ t, W (t, v) ∂μ := integral_integral_swap hWi
  have hsecond : (∫ v : ℝ, ∫ t, W (t, v) ∂μ) ≤
      (∫ v : ℝ, k v) * M := by
    rw [← integral_mul_const]
    apply integral_mono_ae hWi.integral_prod_right (hki.mul_const M)
    apply Filter.Eventually.of_forall
    intro v
    dsimp only [W]
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (hk0 v)
    simpa only [intervalIntegral.integral_of_le hHT, μ] using hM v
  rw [intervalIntegral.integral_of_le hHT]
  change (∫ t, ‖∫ v : ℝ, G (t, v)‖ ^ 2 ∂μ) ≤ _
  calc
    _ ≤ (∫ v : ℝ, k v) * (∫ t, (∫ v : ℝ, W (t, v)) ∂μ) := hfirst
    _ = (∫ v : ℝ, k v) * (∫ v : ℝ, ∫ t, W (t, v) ∂μ) := by rw [hswap]
    _ ≤ (∫ v : ℝ, k v) * ((∫ v : ℝ, k v) * M) :=
      mul_le_mul_of_nonneg_left hsecond hkint
    _ = (∫ v : ℝ, k v) ^ 2 * M := by ring

end MeasureTheory
