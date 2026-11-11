/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ExponentialEnergyConcentration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quadratic uniform integrability from exponential mark tails

Source: Sections 7 and 8 (Fourth) of the user's FRZ strengthening note.
The explicit cutoff error is K exp(-aR)(R² + 2R/a + 2/a²). It gives
uniformly vanishing quadratic tails for varying marked laws. The final
theorem includes the paper's exact 1/(2π) normalization in equation (39).
No weak-limit moment identification is assumed or asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RiemannResearch.Analysis.MarkedEnergyUniformIntegrability

/-- A uniform exponential tail controls the discarded quadratic energy,
with its exact exponential-polynomial cutoff rate. -/
theorem square_tail_lintegral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (K a R : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hR : 0 < R)
    (htail : ∀ t > 0, μ {ω | t < |Y ω|} ≤
      ENNReal.ofReal (K * Real.exp (-a * t))) :
    (∫⁻ ω in {ω | R < |Y ω|}, ENNReal.ofReal ((Y ω)^2) ∂μ) ≤
      ENNReal.ofReal (K * Real.exp (-a * R) * (R^2 + 2*R/a + 2/a^2)) := by
  let E : Set Ω := {ω | R < |Y ω|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hY.abs
  have hbound := MarkedEnergyMarginal.energyMarginal_le_exponential_envelope
    μ μ id Y measurable_id hY (by simp) K a htail hE
  have hmiddle :
      (∫⁻ t in Ioi (0 : ℝ), min (μ E)
        (ENNReal.ofReal (K * Real.exp (-a * t))) * ENNReal.ofReal (2*t)) ≤
      ∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal (K * Real.exp (-a * R)))
        (ENNReal.ofReal (K * Real.exp (-a * t))) * ENNReal.ofReal (2*t) := by
    apply lintegral_mono
    intro t
    exact mul_le_mul' (min_le_min (htail R hR) le_rfl) le_rfl
  have hlast := ExponentialEnergyConcentration.lintegral_exponential_min_le
    (K * Real.exp (-a * R)) K a R (by positivity) hK ha hR.le
  rw [MarkedEnergyMarginal.energyMarginal_apply μ id Y measurable_id hE] at hbound
  refine (hbound.trans hmiddle).trans (hlast.trans_eq ?_)
  congr 1
  field_simp [ha.ne']
  <;> ring

/-- The quantitative discarded-energy envelope tends to zero. -/
theorem quadratic_tail_envelope_tendsto_zero (K a : ℝ) (ha : 0 < a) :
    Tendsto (fun R : ℝ =>
      K * Real.exp (-a * R) * (R^2 + 2*R/a + 2/a^2)) atTop (𝓝 0) := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha
  simp only [Real.rpow_zero, Real.rpow_one, Real.rpow_two, one_mul] at h0 h1 h2
  have h := (h2.add (h1.const_mul (2/a))).add (h0.const_mul (2/a^2))
  have h' := h.const_mul K
  convert h' using 1 <;> first | (ext R; ring) | ring

/-- A family of varying marked laws has uniformly vanishing quadratic tails
whenever its mark tails share exponential constants. This is the moment
uniform-integrability estimate needed for passage to weak marked limits. -/
theorem uniform_quadratic_tail {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : ι → Measure Ω) (Y : ι → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (K a : ℝ) (hK : 0 ≤ K) (ha : 0 < a)
    (htail : ∀ i t, 0 < t → μ i {ω | t < |Y i ω|} ≤
      ENNReal.ofReal (K * Real.exp (-a * t))) :
    ∀ ε > 0, ∃ R₀ > 0, ∀ R ≥ R₀, ∀ i,
      (∫⁻ ω in {ω | R < |Y i ω|}, ENNReal.ofReal ((Y i ω)^2) ∂μ i) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  have hevent := (quadratic_tail_envelope_tendsto_zero K a ha).eventually
    (eventually_lt_nhds hε)
  obtain ⟨A, hA⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 A, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro R hR i
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  exact (square_tail_lintegral_le (μ i) (Y i) (hY i) K a R hK ha hRpos
    (htail i)).trans (ENNReal.ofReal_le_ofReal (hA R ((le_max_right _ _).trans hR)).le)


/-- Equation (39), including the paper's exact factor 1/(2π). -/
theorem scaled_energyMarginal_le_log_square {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (H : Measure X) (θ : Ω → X) (Y : Ω → ℝ)
    (hθ : Measurable θ) (hY : Measurable Y) (hphase : μ.map θ = H)
    (K a h : ℝ) (hh : 0 < h) (hhK : h ≤ K) (ha : 0 < a)
    (htail : ∀ t > 0, μ {ω | t < |Y ω|} ≤
      ENNReal.ofReal (K * Real.exp (-a * t)))
    {E : Set X} (hE : MeasurableSet E) (hmass : H E = ENNReal.ofReal h) :
    (ENNReal.ofReal (1 / (2 * Real.pi)) •
      MarkedEnergyMarginal.energyMarginal μ θ Y) E ≤
      ENNReal.ofReal (h * ((Real.log (K/h))^2 + 2*Real.log (K/h) + 2) /
        (2 * Real.pi * a^2)) := by
  rw [Measure.smul_apply, smul_eq_mul]
  have h := ExponentialEnergyConcentration.energyMarginal_le_log_square
    μ H θ Y hθ hY hphase K a h hh hhK ha htail hE hmass
  refine (mul_le_mul' le_rfl h).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(2*Real.pi))]
  congr 1
  ring

end RiemannResearch.Analysis.MarkedEnergyUniformIntegrability
