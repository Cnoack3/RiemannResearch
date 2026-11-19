/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSelbergSlopeRH
import RiemannResearch.Analysis.ActualQuasiRiemannSupport

/-! # Selberg slopes compared with the continuum contact boundary

The threshold uses only the isolating interval for the algebraic number.
Its comparison with a candidate density slope therefore has no imported
analytic nonvanishing premise.
-/

noncomputable section
open Set Zeta23
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Exact reciprocal slope threshold for improving the contact boundary. -/
theorem selberg_support_improves_continuumContact_iff {a : ℝ} (ha : 0 < a) :
    1 / 2 + 1 / a < continuumContact ↔ 1 / (continuumContact - 1 / 2) < a :=
  selberg_support_improves_iff ha (by linarith [continuumContact_mem.1])

/-- The reciprocal threshold is isolated to 39 decimal places. -/
theorem continuumContact_selbergSlopeThreshold_isolated :
    1 / (continuumContact - 1 / 2) ∈ Ioo
      (2678481583880647807110182550204092347620 / 10^39 : ℝ)
      (2678481583880647807110182550204092347621 / 10^39 : ℝ) := by
  rw [continuumContact,ContinuumContact.contact_eq]
  have h := ContinuumContact.theta_isolated
  have h0 : 0 < ContinuumContact.theta-1/2 := by linarith [ContinuumContact.theta_range.1]
  have hl := h.1
  have hu := h.2
  norm_num [ContinuumContact.lower,ContinuumContact.upper] at hl hu
  constructor
  · apply (lt_div_iff₀ h0).mpr
    linarith only [hu]
  · apply (div_lt_iff₀ h0).mpr
    linarith only [hl]

/-- Any actual positive-slope provider beyond the reciprocal threshold gives
strict support to the left of the continuum contact boundary. -/
theorem zero_re_lt_continuumContact_of_uniformSelbergDensity {a : ℝ} (ha : 0 < a)
    (hD : UniformSelbergDensity a) (hgap : 1 / (continuumContact - 1/2) < a)
    {ρ : ℂ} (hρ : IsNontrivialZero ρ) : ρ.re < continuumContact :=
  (zero_re_le_of_uniformLogLossDensity ha (uniformLogLossDensity_of_uniformSelberg a hD) hρ).trans_lt
    ((selberg_support_improves_continuumContact_iff ha).mpr hgap)

end RiemannResearch.Analysis.ActualZeroOrdinate
