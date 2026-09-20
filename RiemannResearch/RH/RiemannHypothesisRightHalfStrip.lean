import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.RH.NymanAutocorrelationNullity

/-!
# An unconditional right-half-strip criterion for actual RH

Source: the standard functional-equation reflection argument. The zeta
reflection identity and the equivalence with Mathlib's RiemannHypothesis
are supplied by the two imported project modules. No arithmetic estimate
or density converse is an assumption in this formulation bridge.
-/

namespace RiemannResearch.RH

theorem riemannHypothesis_iff_right_half_strip_zero_free :
    RiemannHypothesis ↔
      ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  rw [riemannHypothesis_iff_strip_zeros_on_line]
  constructor
  · intro h s hs h1 hz
    have he := h s hz (by linarith) h1
    linarith
  · intro h s hz h0 h1
    rcases lt_trichotomy s.re (1 / 2 : ℝ) with hl | he | hr
    · have hz' := riemannZeta_one_sub_eq_zero_of_strip hz h0 h1
      have hhalf : (1 / 2 : ℝ) < (1 - s).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have hlt : (1 - s).re < 1 := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      exact False.elim ((h (1 - s) hhalf hlt) hz')
    · exact he
    · exact False.elim ((h s hr h1) hz)

end RiemannResearch.RH
