import RiemannResearch.RH.ThresholdRiemannHypothesis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Stochastic legal approximation, conserved Mellin values, and RH

Source: user-requested stochastic RH continuation, 2026-09-17.
The actual Mellin separation theorem supplies a pathwise obstruction. It survives
arbitrary dependence, adaptive choices, and every finite random observation time.
Positive-probability visits to every error tolerance suffice for actual RH.
The existence of those visits remains an explicit open arithmetic hypothesis.
No independence, stochastic convergence, or moment assumption is hidden in the
hitting criterion. The expectation bound separately requires actual integrability.
-/

noncomputable section
open MeasureTheory
namespace RiemannResearch.RH.Pareto

/-- A hypothetical zero conserves the exact residual Mellin value. -/
theorem legal_residual_mellin_invariant
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A) :
    paretoMellin (hilbertOne - f) s = 1/s := by
  change paretoMellinContinuous s hs (hilbertOne - f) = _
  rw [map_sub]
  change paretoMellin hilbertOne s - paretoMellin f s = _
  rw [paretoMellin_one s hs, paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf,
    sub_zero]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem stochastic_legal_mellin_invariant
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (G : ℕ → Ω → ThresholdHilbert)
    (hG : ∀ n, ∀ᵐ ω ∂μ, G n ω ∈ hilbertLegalClosure A)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᵐ ω ∂μ, ∀ n, paretoMellin (hilbertOne - G n ω) s = 1/s := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [hG n] with ω hω
  exact legal_residual_mellin_invariant A hA s hs hs1 hz hω

theorem stochastic_legal_error_floor
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (G : ℕ → Ω → ThresholdHilbert)
    (hG : ∀ n, ∀ᵐ ω ∂μ, G n ω ∈ hilbertLegalClosure A)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᵐ ω ∂μ, ∀ n, (2*s.re-1)/‖s‖^2 ≤ ‖hilbertOne-G n ω‖^2 := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [hG n] with ω hω
  exact legalClosure_distance_sq_lower_bound_of_zeta A hA s hs hs1 hz hω

/-- This covers all finite random times, so in particular all finite stopping times. -/
theorem stochastic_legal_stopped_error_floor
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (G : ℕ → Ω → ThresholdHilbert)
    (hG : ∀ n, ∀ᵐ ω ∂μ, G n ω ∈ hilbertLegalClosure A)
    (τ : Ω → ℕ)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᵐ ω ∂μ, (2*s.re-1)/‖s‖^2 ≤ ‖hilbertOne-G (τ ω) ω‖^2 := by
  filter_upwards [stochastic_legal_error_floor μ A hA G hG s hs hs1 hz] with ω hω
  exact hω (τ ω)

/-- No sample path outside a null set ever crosses this arithmetic error floor. -/
theorem stochastic_legal_hitting_null_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (G : ℕ → Ω → ThresholdHilbert)
    (hG : ∀ n, ∀ᵐ ω ∂μ, G n ω ∈ hilbertLegalClosure A)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (ε : ℝ) (hε : ε ≤ (2*s.re-1)/‖s‖^2) :
    μ {ω | ∃ n, ‖hilbertOne-G n ω‖^2 < ε} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [stochastic_legal_error_floor μ A hA G hG s hs hs1 hz] with ω hω
  rintro ⟨n, hn⟩
  exact not_lt_of_ge (hε.trans (hω n)) hn

theorem stochastic_legal_expected_error_floor [IsProbabilityMeasure μ]
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (G : Ω → ThresholdHilbert)
    (hG : ∀ᵐ ω ∂μ, G ω ∈ hilbertLegalClosure A)
    (hint : Integrable (fun ω => ‖hilbertOne-G ω‖^2) μ)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2*s.re-1)/‖s‖^2 ≤ ∫ ω, ‖hilbertOne-G ω‖^2 ∂μ := by
  have h := integral_mono_ae (integrable_const ((2*s.re-1)/‖s‖^2)) hint
    (hG.mono (fun _ hω => legalClosure_distance_sq_lower_bound_of_zeta A hA s hs hs1 hz hω))
  simpa using h

/-- Arbitrarily rare success is sufficient; neither rates nor independence are assumed. -/
theorem zeta_ne_zero_of_positive_legal_hitting
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (G : ℕ → Ω → ThresholdHilbert)
    (hG : ∀ n, ∀ᵐ ω ∂μ, G n ω ∈ hilbertLegalClosure A)
    (hhit : ∀ ε : ℝ, 0 < ε → 0 < μ {ω | ∃ n, ‖hilbertOne-G n ω‖^2 < ε})
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hn : 0 < ‖s‖^2 := pow_pos (norm_pos_iff.mpr hs0) 2
  have hc : 0 < (2*s.re-1)/‖s‖^2 := div_pos (by linarith) hn
  have hp := hhit ((2*s.re-1)/‖s‖^2) hc
  rw [stochastic_legal_hitting_null_of_zeta μ A hA G hG s hs hs1 hz _ le_rfl] at hp
  exact (lt_irrefl _ hp)

theorem riemannHypothesis_of_positive_legal_hitting
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (G : ℕ → Ω → ThresholdHilbert)
    (hG : ∀ n, ∀ᵐ ω ∂μ, G n ω ∈ hilbertLegalClosure A)
    (hhit : ∀ ε : ℝ, 0 < ε → 0 < μ {ω | ∃ n, ‖hilbertOne-G n ω‖^2 < ε}) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hright (s : ℂ) (hzs : riemannZeta s = 0) (hslt : s.re < 1) :
      s.re ≤ 1/2 := by
    by_contra h
    have hs : 1/2 < s.re := lt_of_not_ge h
    have hsne : s ≠ 1 := by intro he; simp [he] at hslt
    exact zeta_ne_zero_of_positive_legal_hitting μ A hA G hG hhit s hs hsne hzs
  have hr := Zeta23.zeta_reflect_zero ρ ⟨hz,h0,h1⟩
  have hb := hright ρ hz h1
  have hb' := hright (Zeta23.reflect ρ) hr.1 hr.2.2
  simp [Zeta23.reflect] at hb'
  linarith

end RiemannResearch.RH.Pareto
