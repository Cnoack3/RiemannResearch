import RiemannResearch.RH.CompactFrequencyRigidity
import RiemannResearch.RH.CompactCriticalMixtureAtoms
import RiemannResearch.RH.FiniteCriticalMellinMixtureEnergy

/-!
# Compact-frequency critical-line mixtures have no nonzero finite-energy annihilator

Source: user-provided compact-frequency rigidity argument, 2026-09-21,
Section 4. Actual rigidity reduces the complex density to finitely many
actual critical-line zero atoms. The proved finite critical-mode energy law
then forces every atom coefficient to vanish, hence the density itself
vanishes almost everywhere. No open provider is assumed.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.SpectralObstruction

/-- The complete Section 4 statement, with all analytic and finite-energy
inputs supplied by proved declarations. -/
theorem compactCriticalMixtureTriviality_proved : CompactCriticalMixtureTrivialityTarget := by
  intro T μ a hdata henergy hann
  classical
  letI : IsFiniteMeasure μ := hdata.2.2.2.1
  have hweighted : zetaWeightedDensity (1 / 2) a =ᵐ[μ] 0 :=
    (compactFrequencyRigidity_proved (1 / 2) T μ a hdata).mp hann
  let S : Finset ℝ := criticalZeroFinset T
  let c : S → ℂ := fun t => densityAtomCoefficient μ a t
  let γ : S → ℝ := fun t => t.val
  have hγ : Function.Injective γ := Subtype.val_injective
  have hrepr (n : ℕ) : finiteCriticalMixture c γ n = continuumMixture (1 / 2) μ a n := by
    unfold finiteCriticalMixture
    dsimp [c, γ]
    exact (Finset.sum_attach S (fun t : ℝ => densityAtomCoefficient μ a t *
      mellinMode (MellinFrequency.criticalPoint t) n)).trans
      (continuumMixture_eq_finite_zero_modes T μ a hdata hweighted n).symm
  have hfinite : Summable (fun n => paretoWeight n * ‖finiteCriticalMixture c γ n‖ ^ 2) := by
    simpa only [hrepr] using henergy
  have hc := finite_criticalMixture_coefficients_zero_of_summable c γ hγ hfinite
  have hatoms : ∀ t ∈ S, densityAtomCoefficient μ a t = 0 := by
    intro t ht
    exact hc ⟨t, ht⟩
  have ha : Integrable a μ := hdata.2.2.2.2.1
  have hsupp := critical_density_supported_on_finite_zeros T μ a hdata hweighted
  have hazero := density_zero_of_finite_atom_coefficients μ a ha S hsupp hatoms
  exact ⟨hazero, continuumMixture_eq_zero_of_density_zero (1 / 2) μ a hazero⟩

end RiemannResearch.RH.Pareto.SpectralObstruction
