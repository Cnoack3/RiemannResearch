/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Quadratic marked marginals and conditional variance

Source: Section 7 of the user's FRZ strengthening note. A marked law, its
measurable phase map, and its phase marginal are explicit data. All phase-mark
dependence is retained. The layer cake gives the exact minimum envelope;
the Radon--Nikodym density is characterized on every measurable phase event.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RiemannResearch.Analysis.MarkedEnergyMarginal

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- The quadratic-mark measure pushed forward to the observed phase. -/
def energyMarginal (μ : Measure Ω) (θ : Ω → X) (Y : Ω → ℝ) : Measure X :=
  (μ.withDensity (fun ω => ENNReal.ofReal ((Y ω)^2))).map θ

/-- Finite horizontal energy cannot charge a phase-null set. This applies to
any marked law, without independence between phase and displacement. -/
theorem energyMarginal_absolutelyContinuous (μ : Measure Ω) (θ : Ω → X)
    (Y : Ω → ℝ) (hθ : Measurable θ) :
    energyMarginal μ θ Y ≪ μ.map θ :=
  (withDensity_absolutelyContinuous μ _).map hθ

theorem energyMarginal_apply (μ : Measure Ω) (θ : Ω → X) (Y : Ω → ℝ)
    (hθ : Measurable θ) {E : Set X} (hE : MeasurableSet E) :
    energyMarginal μ θ Y E =
      ∫⁻ ω in θ ⁻¹' E, ENNReal.ofReal ((Y ω)^2) ∂μ := by
  rw [energyMarginal, Measure.map_apply hθ hE, withDensity_apply _ (hθ hE)]

private theorem integral_two_mul (y : ℝ) :
    (∫ t in (0 : ℝ)..y, 2 * t) = y^2 := by
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*t) t := by
    convert (hasDerivAt_id t).pow 2 using 1 <;> first | rfl | simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => 2*t) by fun_prop).intervalIntegrable 0 y)]
  simp

/-- Exact layer cake for the quadratic mark on a measurable phase event. -/
theorem energyMarginal_layercake (μ : Measure Ω) (θ : Ω → X) (Y : Ω → ℝ)
    (hθ : Measurable θ) (hY : Measurable Y)
    {E : Set X} (hE : MeasurableSet E) :
    energyMarginal μ θ Y E =
      ∫⁻ t in Ioi (0 : ℝ), μ ({ω | t < |Y ω|} ∩ θ ⁻¹' E) *
        ENNReal.ofReal (2*t) := by
  rw [energyMarginal_apply μ θ Y hθ hE]
  have h := lintegral_comp_eq_lintegral_meas_lt_mul
    (μ.restrict (θ ⁻¹' E))
    (f := fun ω => |Y ω|) (g := fun t => 2*t)
    (Filter.Eventually.of_forall (fun ω => abs_nonneg (Y ω)))
    hY.abs.aemeasurable
    (fun t ht => (show Continuous (fun t : ℝ => 2*t) by fun_prop).intervalIntegrable 0 t)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (by norm_num) ht.le)
  simp_rw [integral_two_mul, sq_abs] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards with t
  rw [Measure.restrict_apply (measurableSet_lt measurable_const hY.abs)]

/-- Tail control and a known phase marginal give the sharp minimum envelope.
No independence assumption is used; all phase-mark dependence is retained. -/
theorem energyMarginal_le_tail_envelope (μ : Measure Ω) (H : Measure X)
    (θ : Ω → X) (Y : Ω → ℝ)
    (hθ : Measurable θ) (hY : Measurable Y) (hphase : μ.map θ = H)
    (B : ℝ → ℝ≥0∞) (htail : ∀ t > 0, μ {ω | t < |Y ω|} ≤ B t)
    {E : Set X} (hE : MeasurableSet E) :
    energyMarginal μ θ Y E ≤
      ∫⁻ t in Ioi (0 : ℝ), min (H E) (B t) * ENNReal.ofReal (2*t) := by
  rw [energyMarginal_layercake μ θ Y hθ hY hE]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply mul_le_mul' _ le_rfl
  apply le_min
  · calc
      μ ({ω | t < |Y ω|} ∩ θ ⁻¹' E) ≤ μ (θ ⁻¹' E) :=
        measure_mono inter_subset_right
      _ = H E := by rw [← hphase, Measure.map_apply hθ hE]
  · exact (measure_mono inter_subset_left).trans (htail t ht)

/-- Specialization of the sharp envelope to exponential tails. -/
theorem energyMarginal_le_exponential_envelope (μ : Measure Ω) (H : Measure X)
    (θ : Ω → X) (Y : Ω → ℝ)
    (hθ : Measurable θ) (hY : Measurable Y) (hphase : μ.map θ = H)
    (K a : ℝ)
    (htail : ∀ t > 0, μ {ω | t < |Y ω|} ≤ ENNReal.ofReal (K * Real.exp (-a*t)))
    {E : Set X} (hE : MeasurableSet E) :
    energyMarginal μ θ Y E ≤
      ∫⁻ t in Ioi (0 : ℝ),
        min (H E) (ENNReal.ofReal (K * Real.exp (-a*t))) *
          ENNReal.ofReal (2*t) :=
  energyMarginal_le_tail_envelope μ H θ Y hθ hY hphase _ htail hE


/-- Square-integrability of the mark makes its energy marginal finite. -/
theorem energyMarginal_isFinite (μ : Measure Ω) (θ : Ω → X) (Y : Ω → ℝ)
    (hY2 : Integrable (fun ω => (Y ω)^2) μ) :
    IsFiniteMeasure (energyMarginal μ θ Y) := by
  letI : IsFiniteMeasure (μ.withDensity (fun ω => ENNReal.ofReal ((Y ω)^2))) :=
    isFiniteMeasure_withDensity_ofReal hY2.hasFiniteIntegral
  unfold energyMarginal
  infer_instance

/-- Radon--Nikodym density of the conditional quadratic mark. -/
def varianceDensity (μ : Measure Ω) (H : Measure X) (θ : Ω → X) (Y : Ω → ℝ) :
    X → ℝ≥0∞ :=
  (energyMarginal μ θ Y).rnDeriv H

theorem withDensity_varianceDensity (μ : Measure Ω) (H : Measure X) [SigmaFinite H]
    (θ : Ω → X) (Y : Ω → ℝ) (hθ : Measurable θ)
    (hphase : μ.map θ = H) (hY2 : Integrable (fun ω => (Y ω)^2) μ) :
    H.withDensity (varianceDensity μ H θ Y) = energyMarginal μ θ Y := by
  letI := energyMarginal_isFinite μ θ Y hY2
  apply Measure.withDensity_rnDeriv_eq
  rw [← hphase]
  exact energyMarginal_absolutelyContinuous μ θ Y hθ

/-- The density is characterized by all phase events. This is the precise
conditional-second-moment identity and does not assume independence. -/
theorem varianceDensity_set_lintegral (μ : Measure Ω) (H : Measure X) [SigmaFinite H]
    (θ : Ω → X) (Y : Ω → ℝ) (hθ : Measurable θ)
    (hphase : μ.map θ = H) (hY2 : Integrable (fun ω => (Y ω)^2) μ)
    {E : Set X} (hE : MeasurableSet E) :
    (∫⁻ x in E, varianceDensity μ H θ Y x ∂H) =
      ∫⁻ ω in θ ⁻¹' E, ENNReal.ofReal ((Y ω)^2) ∂μ := by
  rw [← withDensity_apply _ hE,
    withDensity_varianceDensity μ H θ Y hθ hphase hY2]
  exact energyMarginal_apply μ θ Y hθ hE

end RiemannResearch.Analysis.MarkedEnergyMarginal
