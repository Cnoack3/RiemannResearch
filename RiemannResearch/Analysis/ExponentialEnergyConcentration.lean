/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MarkedEnergyMarginal
import RiemannResearch.Analysis.FiniteStrictTailSecondMoment
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Tactic.GCongr

/-!
# Sharp logarithmic-square concentration of marked energy

Source: equation (39) in Section 7 of the user's FRZ strengthening note.
The theorem evaluates the minimum tail envelope, with no independence premise.
It is a theorem for a supplied marked law; construction and moment passage
for a subsequential actual-zero marked law are not asserted here.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RiemannResearch.Analysis.ExponentialEnergyConcentration

theorem integral_linear_exponential_Ioi (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) :
    (∫ t in Ioi R, t * Real.exp (-a*t)) =
      (1 + a*R) * Real.exp (-a*R) / a^2 := by
  have htotal : (∫ t in Ioi (0 : ℝ), t * Real.exp (-a*t)) = 1 / a^2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a)
      (by norm_num) ha
    norm_num [Real.Gamma_two] at h
    simpa [neg_mul, one_div_pow] using h
  have hi : IntegrableOn (fun t : ℝ => t * Real.exp (-a*t)) (Ioi (0 : ℝ)) := by
    apply Integrable.of_integral_ne_zero
    rw [htotal]
    positivity
  have hc : Continuous (fun t : ℝ => t * Real.exp (-a*t)) := by fun_prop
  have hs := intervalIntegral.integral_interval_add_Ioi' (hc.intervalIntegrable 0 R)
    (hi.mono_set (Ioi_subset_Ioi hR))
  rw [htotal, FiniteStrictTail.integral_linear_exponential a R ha] at hs
  calc
    _ = 1/a^2 - (1 - (1+a*R)*Real.exp (-a*R))/a^2 := by linarith
    _ = _ := by ring

theorem lintegral_exponential_min_le (h K a R : ℝ)
    (hh : 0 ≤ h) (hK : 0 ≤ K) (ha : 0 < a) (hR : 0 ≤ R) :
    (∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal h)
      (ENNReal.ofReal (K * Real.exp (-a*t))) * ENNReal.ofReal (2*t)) ≤
      ENNReal.ofReal (h*R^2 + 2*K/a^2*(1+a*R)*Real.exp (-a*R)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      by_cases htr : t ≤ R
      · exact Or.inl ⟨ht, htr⟩
      · exact Or.inr (lt_of_not_ge htr)
    · rintro (ht | ht)
      · exact ht.1
      · exact hR.trans_lt ht
  have hd : Disjoint (Ioc (0 : ℝ) R) (Ioi R) :=
    Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht')
  rw [hsplit, lintegral_union measurableSet_Ioi hd]
  have hhead :
      (∫⁻ t in Ioc (0 : ℝ) R, ENNReal.ofReal h * ENNReal.ofReal (2*t)) =
        ENNReal.ofReal (h*R^2) := by
    simp_rw [← ENNReal.ofReal_mul hh]
    have hc : Continuous (fun t : ℝ => h*(2*t)) := by fun_prop
    rw [← ofReal_integral_eq_lintegral_ofReal (hc.intervalIntegrable 0 R).1
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact mul_nonneg hh (by linarith [ht.1]))]
    rw [← intervalIntegral.integral_of_le hR, intervalIntegral.integral_const_mul]
    have hd (t : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*t) t := by
      convert (hasDerivAt_id t).pow 2 using 1 <;> first | rfl | simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((show Continuous (fun t : ℝ => 2*t) by fun_prop).intervalIntegrable 0 R)]
    simp
  have htail :
      (∫⁻ t in Ioi R, ENNReal.ofReal (K*Real.exp (-a*t)) * ENNReal.ofReal (2*t)) =
        ENNReal.ofReal (2*K/a^2*(1+a*R)*Real.exp (-a*R)) := by
    simp_rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_nonneg _))]
    have hi : IntegrableOn (fun t : ℝ => t * Real.exp (-a*t)) (Ioi R) := by
      apply Integrable.of_integral_ne_zero
      rw [integral_linear_exponential_Ioi a R ha hR]
      positivity
    have hfun (t : ℝ) : (K*Real.exp (-a*t))*(2*t) =
        (2*K)*(t*Real.exp (-a*t)) := by ring
    simp_rw [hfun]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul (2*K))
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (by positivity) (mul_nonneg (hR.trans ht.le) (Real.exp_nonneg _)))]
    rw [integral_const_mul, integral_linear_exponential_Ioi a R ha hR]
    congr 1
    ring
  calc
    _ ≤ (∫⁻ t in Ioc (0 : ℝ) R, ENNReal.ofReal h * ENNReal.ofReal (2*t)) +
        ∫⁻ t in Ioi R, ENNReal.ofReal (K*Real.exp (-a*t)) * ENNReal.ofReal (2*t) := by
      apply add_le_add
      · apply lintegral_mono
        intro t
        exact mul_le_mul' (min_le_left _ _) le_rfl
      · apply lintegral_mono
        intro t
        exact mul_le_mul' (min_le_right _ _) le_rfl
    _ = _ := by
      rw [hhead, htail, ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- Closed-form sharp logarithmic concentration from an exponential marked
tail and a phase marginal. This is the unscaled numerator in equation (39). -/
theorem energyMarginal_le_log_square {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (H : Measure X) (θ : Ω → X) (Y : Ω → ℝ)
    (hθ : Measurable θ) (hY : Measurable Y) (hphase : μ.map θ = H)
    (K a h : ℝ) (hh : 0 < h) (hhK : h ≤ K) (ha : 0 < a)
    (htail : ∀ t > 0, μ {ω | t < |Y ω|} ≤ ENNReal.ofReal (K*Real.exp (-a*t)))
    {E : Set X} (hE : MeasurableSet E) (hmass : H E = ENNReal.ofReal h) :
    MarkedEnergyMarginal.energyMarginal μ θ Y E ≤
      ENNReal.ofReal (h/a^2*((Real.log (K/h))^2 + 2*Real.log (K/h) + 2)) := by
  have hK : 0 < K := hh.trans_le hhK
  have hratio : 1 ≤ K/h := (le_div_iff₀ hh).mpr (by simpa using hhK)
  have hlog : 0 ≤ Real.log (K/h) := Real.log_nonneg hratio
  let R := Real.log (K/h) / a
  have hR : 0 ≤ R := div_nonneg hlog ha.le
  have hcrit : K * Real.exp (-a*R) = h := by
    have heq : -a*R = -(Real.log (K/h)) := by dsimp [R]; field_simp [ha.ne']
    rw [heq, Real.exp_neg, Real.exp_log (div_pos hK hh)]
    field_simp [hh.ne', hK.ne']
  have hbound := MarkedEnergyMarginal.energyMarginal_le_exponential_envelope
    μ H θ Y hθ hY hphase K a htail hE
  rw [hmass] at hbound
  refine hbound.trans ((lintegral_exponential_min_le h K a R hh.le hK.le ha hR).trans_eq ?_)
  congr 1
  calc
    h*R^2 + 2*K/a^2*(1+a*R)*Real.exp (-a*R) =
        h*R^2 + (2*(1+a*R)/a^2)*(K*Real.exp (-a*R)) := by ring
    _ = h*R^2 + (2*(1+a*R)/a^2)*h := by rw [hcrit]
    _ = _ := by dsimp [R]; field_simp; ring


theorem energyMarginal_finite_of_exponential {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (H : Measure X) [IsProbabilityMeasure H]
    (θ : Ω → X) (Y : Ω → ℝ) (hθ : Measurable θ) (hY : Measurable Y)
    (hphase : μ.map θ = H) (K a : ℝ) (hK : 1 ≤ K) (ha : 0 < a)
    (htail : ∀ t > 0, μ {ω | t < |Y ω|} ≤ ENNReal.ofReal (K*Real.exp (-a*t))) :
    IsFiniteMeasure (MarkedEnergyMarginal.energyMarginal μ θ Y) := by
  constructor
  have h := energyMarginal_le_log_square μ H θ Y hθ hY hphase K a 1
    zero_lt_one hK ha htail (E := Set.univ) MeasurableSet.univ (by simp)
  exact h.trans_lt (by simp)

/-- The exponential tail alone supplies the finite density representation;
no extra square-integrability premise is required. -/
theorem varianceDensity_representation_of_exponential {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (H : Measure X) [IsProbabilityMeasure H]
    (θ : Ω → X) (Y : Ω → ℝ) (hθ : Measurable θ) (hY : Measurable Y)
    (hphase : μ.map θ = H) (K a : ℝ) (hK : 1 ≤ K) (ha : 0 < a)
    (htail : ∀ t > 0, μ {ω | t < |Y ω|} ≤ ENNReal.ofReal (K*Real.exp (-a*t))) :
    H.withDensity (MarkedEnergyMarginal.varianceDensity μ H θ Y) =
      MarkedEnergyMarginal.energyMarginal μ θ Y := by
  letI := energyMarginal_finite_of_exponential μ H θ Y hθ hY hphase K a hK ha htail
  apply Measure.withDensity_rnDeriv_eq
  rw [← hphase]
  exact MarkedEnergyMarginal.energyMarginal_absolutelyContinuous μ θ Y hθ

end RiemannResearch.Analysis.ExponentialEnergyConcentration
