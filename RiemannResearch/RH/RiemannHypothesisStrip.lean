import RiemannResearch.RH.WeilExplicitFormula.RvM.CountByIntegral

/-!
# Mathlib's Riemann hypothesis and its open-strip formulation

The proof uses the actual completed-zeta zero characterization already proved
in the project and Mathlib's Gamma-factor zero characterization. The latter
API and statement are documented at
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.html
This is a standard formulation bridge, not an assumption about zeta zeros.
-/

namespace RiemannResearch.RH

/-- The standard equivalence between Mathlib's exclusion-of-trivial-zeros
definition and the open-critical-strip formulation. Boundary zero-freeness
and the Gamma factor's artificial zeros are discharged by actual providers. -/
theorem riemannHypothesis_iff_strip_zeros_on_line :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  constructor
  · intro hRH s hz h0 h1
    exact Zeta23.RH_implies_on_line hRH ⟨hz, h0, h1⟩
  · intro hstrip s hz hnot _
    have hs0 : s ≠ 0 := by
      intro he
      norm_num [he, riemannZeta_zero] at hz
    have hGamma : Complex.Gammaℝ s ≠ 0 := by
      intro hG
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hG
      cases n with
      | zero =>
          apply hs0
          simpa using hn
      | succ n =>
          apply hnot
          refine ⟨n, ?_⟩
          rw [hn]
          push_cast
          ring
    have hc : completedRiemannZeta s = 0 := by
      rw [Zeta23.RvM.completedRiemannZeta_eq_Gammaℝ_mul hs0 hGamma, hz, mul_zero]
    have hs := Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mp hc
    exact hstrip s hs.1 hs.2.1 hs.2.2

end RiemannResearch.RH
