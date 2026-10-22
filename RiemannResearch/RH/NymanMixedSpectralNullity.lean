import RiemannResearch.RH.NymanActualZeroSumNullity
import RiemannResearch.Analysis.SmoothCorrelationClosure

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Both mixed spectral pairings of actual completed Nyman tests vanish

The first orientation uses the functional equation; the other uses zeta's
proved conjugation symmetry. This supplies radical nullity, rather than only
vanishing of the quadratic self-pairing, once the noncompact explicit formula
is applied. The comparison test is an arbitrary smooth-superexponential test.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis
open scoped ComplexConjugate

namespace MeasureTheory.BilateralLaplace

theorem centeredTransform_crossCorrelation {f g : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hg : HasExponentialMoments g)
    (hfc : Continuous f) (hgc : Continuous g) (s : ℂ) :
    centeredTransform (RiemannResearch.Analysis.crossCorrelation f g) s =
      centeredTransform f s * conj (centeredTransform g (1 - conj s)) := by
  have harg : ((1 - conj s) - 1 / 2) = -conj (s - 1 / 2) := by
    apply Complex.ext <;> simp <;> ring
  change transform (RiemannResearch.Analysis.crossCorrelation f g) (s - 1 / 2) =
    transform f (s - 1 / 2) * conj (transform g ((1 - conj s) - 1 / 2))
  rw [harg]
  exact transform_crossCorrelation hf hg hfc hgc (s - 1 / 2)

end MeasureTheory.BilateralLaplace

namespace RiemannResearch.RH

theorem paperFT_gammaOf_nymanCompletedTest_crossCorrelation_left_zero
    (n M : ℕ) (hn : 2 ≤ n) {v g : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    (hg : SmoothSuperexponentialDecay g) (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.paperFT (RiemannResearch.Analysis.crossCorrelation (nymanCompletedTest n M hn v) g)
      (Zeta23.gammaOf ρ) = 0 := by
  have hG := smoothSuperexponentialDecay_nymanCompletedTest n M hn hv ha hb
  have hρ : riemannZeta (ρ : ℂ) = 0 ∧ 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ρ.property
  have hreflect : riemannZeta (1 - (ρ : ℂ)) = 0 :=
    riemannZeta_one_sub_eq_zero_of_strip hρ.1 hρ.2.1 hρ.2.2
  have hne : 1 - (ρ : ℂ) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith [hρ.2.1]
  rw [WeilExplicitFormula.paperFT_gammaOf_eq_centeredTransform,
    centeredTransform_crossCorrelation
      (hG.decay.hasExponentialMoments hG.1.continuous)
      (hg.decay.hasExponentialMoments hg.1.continuous) hG.1.continuous hg.1.continuous,
    centeredTransform_nymanCompletedTest_zero n M hn hv ha hb hne hreflect, zero_mul]

theorem paperFT_gammaOf_nymanCompletedTest_crossCorrelation_right_zero
    (n M : ℕ) (hn : 2 ≤ n) {v g : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    (hg : SmoothSuperexponentialDecay g) (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.paperFT (RiemannResearch.Analysis.crossCorrelation g (nymanCompletedTest n M hn v))
      (Zeta23.gammaOf ρ) = 0 := by
  have hG := smoothSuperexponentialDecay_nymanCompletedTest n M hn hv ha hb
  have hρ : riemannZeta (ρ : ℂ) = 0 ∧ 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ρ.property
  have hne : (ρ : ℂ) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith [hρ.2.2]
  have hcne : conj (ρ : ℂ) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith [hρ.2.2]
  have hconj : riemannZeta (conj (ρ : ℂ)) = 0 := by
    rw [Zeta23.riemannZeta_conj hne, hρ.1]
    simp
  have harg : 1 - conj (1 - (ρ : ℂ)) = conj (ρ : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [WeilExplicitFormula.paperFT_gammaOf_eq_centeredTransform,
    centeredTransform_crossCorrelation
      (hg.decay.hasExponentialMoments hg.1.continuous)
      (hG.decay.hasExponentialMoments hG.1.continuous) hg.1.continuous hG.1.continuous,
    harg, centeredTransform_nymanCompletedTest_zero n M hn hv ha hb hcne hconj,
    map_zero, mul_zero]

theorem actual_zero_sums_nymanCompletedTest_mixed_zero
    (n M : ℕ) (hn : 2 ≤ n) {v g : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    (hg : SmoothSuperexponentialDecay g) :
    (∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT
        (RiemannResearch.Analysis.crossCorrelation (nymanCompletedTest n M hn v) g)
        (Zeta23.gammaOf ρ)) = 0 ∧
    (∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT
        (RiemannResearch.Analysis.crossCorrelation g (nymanCompletedTest n M hn v))
        (Zeta23.gammaOf ρ)) = 0 := by
  simp only [paperFT_gammaOf_nymanCompletedTest_crossCorrelation_left_zero n M hn hv ha hb hg,
    paperFT_gammaOf_nymanCompletedTest_crossCorrelation_right_zero n M hn hv ha hb hg,
    mul_zero, tsum_zero, and_self]

theorem actual_zero_sums_nymanCompletedTest_mixed_summable
    (n M : ℕ) (hn : 2 ≤ n) {v g : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    (hg : SmoothSuperexponentialDecay g) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      ‖(Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT
        (RiemannResearch.Analysis.crossCorrelation (nymanCompletedTest n M hn v) g)
        (Zeta23.gammaOf ρ)‖) ∧
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      ‖(Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT
        (RiemannResearch.Analysis.crossCorrelation g (nymanCompletedTest n M hn v))
        (Zeta23.gammaOf ρ)‖) := by
  simp only [paperFT_gammaOf_nymanCompletedTest_crossCorrelation_left_zero n M hn hv ha hb hg,
    paperFT_gammaOf_nymanCompletedTest_crossCorrelation_right_zero n M hn hv ha hb hg,
    mul_zero, norm_zero, summable_zero, and_self]

end RiemannResearch.RH
