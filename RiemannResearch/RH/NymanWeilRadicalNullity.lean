import RiemannResearch.RH.WeilNoncompactExplicitFormula
import RiemannResearch.RH.NymanMixedSpectralNullity

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual mixed arithmetic Weil pairings vanish in both orientations

The literal arithmetic expression contains the actual infinite von Mangoldt
sum, both polar values, and the full digamma integral. This theorem identifies
its value through the proved noncompact explicit formula and the proved
actual arithmetic channel transform nullity.
-/

open RiemannResearch.Analysis

namespace RiemannResearch.RH

theorem literatureRHS_nymanCompletedTest_mixed_eq_zero
    (n M : ℕ) (hn : 2 ≤ n) {v g : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    (hg : SmoothSuperexponentialDecay g) :
    Zeta23.EF.literatureRHS
      (RiemannResearch.Analysis.crossCorrelation (nymanCompletedTest n M hn v) g) = 0 ∧
    Zeta23.EF.literatureRHS
      (RiemannResearch.Analysis.crossCorrelation g (nymanCompletedTest n M hn v)) = 0 := by
  have hG := smoothSuperexponentialDecay_nymanCompletedTest n M hn hv ha hb
  have hz := actual_zero_sums_nymanCompletedTest_mixed_zero n M hn hv ha hb hg
  constructor
  · exact (SignedWeilCorrelation.actual_noncompact_literal_Weil_explicit_formula
      (hG.crossCorrelation hg)).symm.trans hz.1
  · exact (SignedWeilCorrelation.actual_noncompact_literal_Weil_explicit_formula
      (hg.crossCorrelation hG)).symm.trans hz.2

end RiemannResearch.RH
