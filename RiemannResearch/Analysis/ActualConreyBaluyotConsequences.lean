/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSelbergDensityConventions

/-!
# Quantitative consequences throughout the Conrey--Baluyot range

The published density range is 0 < a < 8/7, not a = 8/7.
For every fixed frequency-band width b < 8/7 one can choose b < a < 8/7.
The resulting constants depend on b and on the density provider.
The analytic provider remains an explicit hypothesis; this module does not
claim to formalize Baluyot's mollified zeta moment or Kloosterman estimates.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Direct band-width formulation, retaining the exact positive denominator. -/
theorem normalized_ordinate_landau_error_of_density_width
    (T u C a b : ℝ) (hT : 1 < T) (hC : 0 ≤ C)
    (hb : 0 ≤ b) (hba : b < a)
    (hu : |u| ≤ b * Real.log T) (hD : SelbergDensityBound T C a) :
    ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
      (2 * C / (a ^ 2 - b ^ 2)) * u ^ 2 / Real.log T := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hθ : b / a < 1 := (div_lt_one ha).mpr hba
  have hu' : |u| ≤ (b / a) * (a * Real.log T) := by
    simpa only [← mul_assoc, div_mul_cancel₀ b ha.ne'] using hu
  have h := normalized_ordinate_landau_error_of_selbergDensity_band
    T u C a (b / a) hT hC ha (div_nonneg hb ha.le) hθ hu' hD
  have heq : a ^ 2 * (1 - (b / a) ^ 2) = a ^ 2 - b ^ 2 := by
    field_simp [ha.ne']
  rwa [heq] at h

/-- One constant controls every frequency in a fixed band b log T.
Only b < a is required; no artificial one-quarter restriction survives. -/
theorem eventually_ordinate_landau_error_of_uniform_density_width
    (a b : ℝ) (hb : 0 ≤ b) (hba : b < a)
    (hD : UniformSelbergDensity a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ,
      |u| ≤ b * Real.log T →
      ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
        K * u ^ 2 / Real.log T := by
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  have hden : 0 < a ^ 2 - b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hba) (by linarith : 0 < a + b)]
  refine ⟨2 * C / (a ^ 2 - b ^ 2), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T₀] with T hT u hu
  exact normalized_ordinate_landau_error_of_density_width T u C a b
    (hT₀.trans_le hT) hC hb hba hu (hD T hT)

/-- Full open published frequency range, with a fixed interior density exponent.
There is no claim of constants uniform as b tends to 8/7. -/
theorem ConreyBaluyotDensityHypothesis.frequency_band
    (hD : ConreyBaluyotDensityHypothesis) (b : ℝ)
    (hb : 0 ≤ b) (hb' : b < 8 / 7) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ,
      |u| ≤ b * Real.log T →
      ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
        K * u ^ 2 / Real.log T := by
  let a : ℝ := (b + 8 / 7) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hba : b < a := by dsimp [a]; linarith
  have ha' : a < 8 / 7 := by dsimp [a]; linarith
  exact eventually_ordinate_landau_error_of_uniform_density_width a b hb hba
    (hD a ha ha')

/-- Moving frequencies are allowed when their complete quadratic budget tends
to zero. This limit is conditional on the analytic density provider. -/
theorem tendsto_ordinate_landau_error_of_moving_density_band
    (a b : ℝ) (u : ℝ → ℝ) (hb : 0 ≤ b) (hba : b < a)
    (hD : UniformSelbergDensity a)
    (hband : ∀ᶠ T : ℝ in atTop, |u T| ≤ b * Real.log T)
    (hbudget : Tendsto (fun T : ℝ => (u T) ^ 2 / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (ordinateSum T (u T) - landauSum T (u T)) / (T : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ :=
    eventually_ordinate_landau_error_of_uniform_density_width a b hb hba hD
  apply squeeze_zero_norm'
  · filter_upwards [hbound, hband] with T hT hbT
    simpa only [mul_div_assoc] using hT (u T) hbT
  · simpa only [mul_zero] using hbudget.const_mul K

/-- A fixed-mode comparison requires only some positive density exponent.
The classical value 1/4 is not logically necessary. -/
theorem tendsto_ordinate_landau_error_of_positive_density
    (a u : ℝ) (ha : 0 < a) (hD : UniformSelbergDensity a) :
    Tendsto (fun T : ℝ => (ordinateSum T u - landauSum T u) / (T : ℂ))
      atTop (𝓝 0) := by
  apply tendsto_ordinate_landau_error_of_moving_density_band a (a / 2)
    (fun _ => u) (by positivity) (by linarith) hD
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (2 * |u| / a)] with T hT
    have := mul_le_mul_of_nonneg_left hT (show 0 ≤ a / 2 by positivity)
    have heq : (a / 2) * (2 * |u| / a) = |u| := by field_simp [ha.ne']
    rwa [heq] at this
  · exact Real.tendsto_log_atTop.const_div_atTop (u ^ 2)

end RiemannResearch.Analysis.ActualZeroOrdinate
