import RiemannResearch.RH.MellinZeroProfile

/-!
# The unscaled Mellin-window RH test and its exact provider boundary

Source: ArithmeticProjectionDPPDraft20260921.md (2026-09-21), Section
7.2. The deficit is the actual coordinate-cutoff defect defined in the
companion module. The asymptotic criterion uses ENNReal liminf.

The one-coordinate test implies Mathlib RH without any extra provider.
The asymptotic RH equivalence below is a CONDITIONAL RESEARCH REDUCTION:
the analytic zero-profile bounds and the classical RH-to-residue-density
converse are explicit arguments, not axioms or silently assumed theorems.
The latter is a formalization gap in the current project, not a new
mathematical conjecture. Vanishing of the deficit without RH remains open.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace RiemannResearch.RH.Pareto.CoordinateMellin
open CoefficientStabilization IntegerDPP MellinFrequency
open RiemannResearch.Analysis.NonnegativeDeficit

def WindowTest (I : Set ℝ) : Prop :=
  Filter.liminf (fun M => windowDeficit M I) atTop = 0

theorem windowTest_iff_cofinallySmall (I : Set ℝ) :
    WindowTest I ↔ ∀ ε : ℝ≥0∞, 0 < ε → ∀ N : ℕ,
      ∃ M, N ≤ M ∧ windowDeficit M I < ε :=
  liminf_eq_zero_iff_cofinallySmall _

theorem windowTest_of_density (h : closedSpace = ⊤) (I : Set ℝ) : WindowTest I := by
  unfold WindowTest
  simp only [windowDeficit_zero_of_top h]
  exact Filter.liminf_const 0

theorem all_windows_zero_iff_density (I : Set ℝ) (hI : 0 < frequencyMeasure I) :
    (∀ M, windowDeficit M I = 0) ↔ closedSpace = ⊤ := by
  constructor
  · intro h
    exact (first_window_zero_iff_density I hI).mp (h 1)
  · intro h M
    exact windowDeficit_zero_of_top h M I

/-- Precise analytic obligations from the informal zero-mode proof.
These fields are not constructed in this module. All refer to explicit
coordinate features and the actual residue projection. -/
structure ZeroModeWindowProvider (I : Set ℝ) : Prop where
  profile_converges : ∀ ρ : ℂ, (1 / 2 : ℝ) < ρ.re → ∀ t,
    Tendsto (fun M => zeroProfilePartial ρ M t) atTop (𝓝 (zeroProfile ρ t))
  window_mass_pos : ∀ ρ : ℂ, (1 / 2 : ℝ) < ρ.re → 0 < zeroWindowMass ρ I

theorem liminf_pos_of_offcritical_zero (I : Set ℝ)
    (hp : ZeroModeWindowProvider I) (ρ : ℂ)
    (hρ : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    0 < Filter.liminf (fun M => windowDeficit M I) atTop :=
  (hp.window_mass_pos ρ hρ).trans_le
    (zeroWindowMass_le_liminf ρ I hρ
      (by intro he; simp [he] at hρ1) hz (hp.profile_converges ρ hρ))

/-- CONDITIONAL RESEARCH REDUCTION: the zero-profile provider is explicit.
This proves Mathlib RH from the unscaled test once those analytic facts
have been kernel-checked for the actual profiles. -/
theorem riemannHypothesis_of_windowTest (I : Set ℝ)
    (hp : ZeroModeWindowProvider I) (h : WindowTest I) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro ρ hρ hρ1 hz
  have hpos := liminf_pos_of_offcritical_zero I hp ρ hρ hρ1 hz
  rw [h] at hpos
  exact (lt_irrefl _) hpos

/-- CONDITIONAL RESEARCH REDUCTION, with both missing formalization
dependencies exposed in its type. It is not an unconditional proof of RH. -/
theorem riemannHypothesis_iff_windowTest (I : Set ℝ)
    (hDensity : RiemannHypothesis → closedSpace = ⊤)
    (hp : ZeroModeWindowProvider I) : RiemannHypothesis ↔ WindowTest I :=
  ⟨fun h => windowTest_of_density (hDensity h) I,
    riemannHypothesis_of_windowTest I hp⟩

theorem riemannHypothesis_iff_first_window_zero (I : Set ℝ)
    (hI : 0 < frequencyMeasure I)
    (hDensity : RiemannHypothesis → closedSpace = ⊤) :
    RiemannHypothesis ↔ windowDeficit 1 I = 0 :=
  ⟨fun h => windowDeficit_zero_of_top (hDensity h) 1 I,
    riemannHypothesis_of_first_window_zero I hI⟩

end RiemannResearch.RH.Pareto.CoordinateMellin
