import RiemannResearch.RH.CauchyMixtureEscape
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# The exact Cauchy-annihilator criterion for Mathlib RH

Source: user-requested RH proof/obstruction audit, 2026-09-21. This module
combines the coordinate Cauchy-mixture construction and its proved energy
and residue-pairing identities with the functional-equation half-strip
criterion. It supplies no new zero or zero-free estimate.

The equivalences below are unconditional theorems about Mathlib's actual
RiemannHypothesis: they assume neither RH nor an RH-to-density provider.
The existence/nonexistence of the displayed annihilator remains open.
In particular, compact-frequency and countable first-moment exclusions
cannot be applied to these continuous unbounded-frequency Cauchy mixtures.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace RiemannResearch.RH.Pareto.SpectralObstruction

/-- Every point in the open right half-strip has positive Cauchy coordinates. -/
theorem exists_cauchy_coordinates (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hupper : s.re < 1) :
    ∃ (δ : ℝ≥0) (γ : ℝ), δ ≠ 0 ∧ (δ : ℝ) < 1 / 2 ∧
      cauchyMellinPoint δ γ = s := by
  let δ : ℝ≥0 := ⟨s.re - 1 / 2, by linarith⟩
  have hδ : δ ≠ 0 := by
    intro he
    have h := congrArg (fun x : ℝ≥0 => (x : ℝ)) he
    change s.re - 1 / 2 = 0 at h
    linarith
  refine ⟨δ, s.im, hδ, ?_, ?_⟩
  · change s.re - 1 / 2 < 1 / 2
    linarith
  · apply Complex.ext
    · rw [cauchyMellinPoint_re]
      change 1 / 2 + (s.re - 1 / 2) = s.re
      ring
    · simp [cauchyMellinPoint, verticalPoint]

/-- Exact equivalence with failure of Mathlib RH, with nonzero finite-energy
and arithmetic annihilation all required of the same concrete mixture. -/
theorem not_RH_iff_exists_finite_energy_cauchy_annihilator :
    ¬ RiemannHypothesis ↔
      ∃ (δ : ℝ≥0) (γ : ℝ), δ ≠ 0 ∧ (δ : ℝ) < 1 / 2 ∧
        cauchyMellinMixture δ γ ≠ 0 ∧
        Summable (fun n : ℕ => paretoWeight n * ‖cauchyMellinMixture δ γ n‖ ^ 2) ∧
        (0 < ∑' n : ℕ, paretoWeight n * ‖cauchyMellinMixture δ γ n‖ ^ 2) ∧
        (∀ d : ℕ, 2 ≤ d → residuePairing (cauchyMellinMixture δ γ) d = 0) := by
  constructor
  · intro hRH
    have hz : ¬ (∀ s : ℂ, (1 / 2 : ℝ) < s.re → s.re < 1 → riemannZeta s ≠ 0) := by
      intro hf
      exact hRH (RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr hf)
    push Not at hz
    obtain ⟨s, hs, h1, hz⟩ := hz
    obtain ⟨δ, γ, hδ, hupper, he⟩ := exists_cauchy_coordinates s hs h1
    refine ⟨δ, γ, hδ, hupper, cauchyMellinMixture_ne_zero δ γ hδ,
      cauchyMellinMixture_energy_summable δ γ hδ,
      cauchyMellinMixture_energy_pos δ γ hδ, ?_⟩
    apply (cauchyMellinMixture_annihilates_iff δ γ hδ hupper).mpr
    rwa [he]
  · rintro ⟨δ, γ, hδ, hupper, _, _, _, hann⟩ hRH
    have hz := (cauchyMellinMixture_annihilates_iff δ γ hδ hupper).mp hann
    apply (RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mp hRH)
      (cauchyMellinPoint δ γ) (cauchyMellinPoint_re_gt_half δ γ hδ) _ hz
    rw [cauchyMellinPoint_re]
    linarith

/-- The single d=2 pairing detects all Cauchy mixtures exactly when RH holds.
The nonvanishing assertion itself remains unproved. -/
theorem riemannHypothesis_iff_cauchy_generator_detected :
    RiemannHypothesis ↔
      ∀ (δ : ℝ≥0) (γ : ℝ), δ ≠ 0 → (δ : ℝ) < 1 / 2 →
        residuePairing (cauchyMellinMixture δ γ) 2 ≠ 0 := by
  constructor
  · intro hRH δ γ hδ hupper
    rw [cauchyMellinMixture_residuePairing δ γ hδ hupper 2 (by omega)]
    have hsupper : (cauchyMellinPoint δ γ).re < 1 := by
      rw [cauchyMellinPoint_re]
      linarith
    exact mul_ne_zero (residue_factor_two_ne_zero_of_re_lt_one _ hsupper)
      ((RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mp hRH)
        _ (cauchyMellinPoint_re_gt_half δ γ hδ) hsupper)
  · intro h
    by_contra hRH
    obtain ⟨δ, γ, hδ, hupper, _, _, _, hann⟩ :=
      not_RH_iff_exists_finite_energy_cauchy_annihilator.mp hRH
    exact h δ γ hδ hupper (hann 2 (by omega))

end RiemannResearch.RH.Pareto.SpectralObstruction
