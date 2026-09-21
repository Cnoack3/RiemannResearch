import RiemannResearch.RH.CompactMixtureResidueIdentity
import RiemannResearch.RH.WeightedDensityFourierUniqueness
import RiemannResearch.RH.LogIntegerSamplingUniqueness

/-!
# Compact-frequency Mellin rigidity with all analytic inputs discharged

Source: the user's compact-frequency obstruction argument, 2026-09-21.
The Mellin summation identity, compact Fourier growth, Fourier uniqueness,
and logarithmic integer sampling theorem are all proved in imported modules.
The result below assumes only the actual compact-frequency data.
-/

noncomputable section
open MeasureTheory

namespace RiemannResearch.RH.Pareto.SpectralObstruction

/-- All three formerly separate analytic obligations follow from the actual
compact-frequency hypotheses. -/
theorem compactMixtureAnalyticProvider_proved : CompactMixtureAnalyticProvider := by
  intro σ T μ a hdata
  exact ⟨mixtureResidueIdentity_of_compact_data σ T μ a hdata,
    samplingDefect_entireExponentialType σ T μ a hdata,
    weightedFourierUniqueness_of_integrable σ μ a
      (zetaWeightedDensity_integrable σ T μ a hdata)⟩

/-- Compact-frequency mixtures annihilate every normalized residue precisely
when their zeta-weighted density vanishes almost everywhere. -/
theorem compactFrequencyRigidity_proved : CompactFrequencyRigidityTarget :=
  compactFrequencyRigidity_of_analyticProvider compactMixtureAnalyticProvider_proved

end RiemannResearch.RH.Pareto.SpectralObstruction
