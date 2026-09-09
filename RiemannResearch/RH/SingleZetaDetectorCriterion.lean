import RiemannResearch.Analysis.SubpowerTailObstruction
import RiemannResearch.Analysis.BilateralLaplaceTranslation
import RiemannResearch.RH.WeilSpectralPairing
import RiemannResearch.RH.RiemannHypothesisStrip

/-!
# A single-test Riemann-hypothesis criterion for arbitrary actual tails

Source: user-provided RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md,
sections 1–2 (statement and proof strategy). This conditional research reduction
assumes detector nonvanishing, actual tail L² membership, support, exact
transform cancellation, and subpower growth. It does not construct any of
these data. In particular, it does not identify a mixed two-conductor family
with the canonical one-conductor family.
-/

open MeasureTheory Filter
open scoped Topology

namespace RiemannResearch.RH

open MeasureTheory.BilateralLaplace

/-- Conditional single-test criterion for arbitrary actual tails. It covers
the mixed-conductor optimizer only after its L², support, spectral cancellation
and growth hypotheses are supplied. Detector existence is also not asserted.
The zero set and reflection in the conclusion are those of the actual zeta. -/
theorem riemannHypothesis_of_single_zeta_detecting_subpower_tail_test
    {f : ℝ → ℂ} {τ : ℕ → ℝ → ℂ} {a : ℝ}
    (hLp : ∀ M, MemLp (τ M) 2 volume)
    (hsupport : ∀ M y, y < a + Real.log (M + 1 : ℕ) → τ M y = 0)
    (hsignature : ∀ (M : ℕ) (s : ℂ), riemannZeta s = 0 →
      0 < s.re → s.re < 1 → centeredTransform (τ M) s = -centeredTransform f s)
    (hdetect : ∀ s : ℂ, riemannZeta s = 0 →
      0 < s.re → s.re < 1 → centeredTransform f s ≠ 0)
    (hgrowth : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun M : ℕ => Real.exp (-ε * Real.log (M + 1 : ℕ)) *
        RemoteLaplaceTail.energy (τ M)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hright (s : ℂ) (hsz : riemannZeta s = 0)
      (hs0 : 0 < s.re) (hs1 : s.re < 1) : s.re ≤ 1 / 2 := by
    by_contra h
    have hs : 1 / 2 < s.re := lt_of_not_ge h
    apply hdetect s hsz hs0 hs1
    apply RemoteLaplaceTail.signature_eq_zero_of_supported_subpower_tail
      hs hLp hsupport (centeredTransform f s) _ hgrowth
    intro M
    exact hsignature M s hsz hs0 hs1
  have hr := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hrbound := hright (Zeta23.reflect ρ) hr.1 hr.2.1 hr.2.2
  have hbnd := hright ρ hz h0 h1
  simp [Zeta23.reflect] at hrbound
  linarith

end RiemannResearch.RH
