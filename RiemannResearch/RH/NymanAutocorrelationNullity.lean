import RiemannResearch.RH.NymanTransformNullity
import RiemannResearch.RH.NymanCompletionAdmissibility
import RiemannResearch.RH.WeilCorrelationTransform

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual Nyman autocorrelations annihilate both spectral and polar terms

The reflected zero is derived from Mathlib's unconditional zeta functional
equation. The transform and regularity hypotheses of the correlation theorem
are supplied by the actual arithmetic completion. No RH or reflected-zero
assumption is used.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis

namespace RiemannResearch.RH

theorem riemannZeta_one_sub_eq_zero_of_strip {s : ℂ}
    (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = 0 := by
  have hneg (n : ℕ) : s ≠ -(n : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at h1
  rw [riemannZeta_one_sub hneg hs1, hz, mul_zero]

private theorem one_sub_ne_one_of_re_pos {s : ℂ} (h0 : 0 < s.re) : 1 - s ≠ 1 := by
  intro h
  have hs0 : s = 0 := by
    calc
      s = 1 - (1 - s) := by ring
      _ = 0 := by rw [h]; ring
  subst s
  norm_num at h0

theorem realAutocorrelation_nymanCompletedTest_centeredTransform_zero
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    centeredTransform
      (fun t => (SignedWeilCorrelation.realAutocorrelation (nymanCompletedTest n M hn v) t : ℂ))
      s = 0 := by
  have hG := smoothSuperexponentialDecay_nymanCompletedTest n M hn hv ha hb
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at h1
  have hzR := riemannZeta_one_sub_eq_zero_of_strip hz h0 h1
  exact SignedWeilCorrelation.realAutocorrelation_transform_zero
    hG.decay hG.deriv.decay (hG.1.differentiable (by simp)) s
    (centeredTransform_nymanCompletedTest_zero n M hn hv ha hb hs1 hz)
    (centeredTransform_nymanCompletedTest_zero n M hn hv ha hb
      (one_sub_ne_one_of_re_pos h0) hzR)

theorem realAutocorrelation_nymanCompletedTest_centeredTransform_polar
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    centeredTransform
      (fun t => (SignedWeilCorrelation.realAutocorrelation (nymanCompletedTest n M hn v) t : ℂ))
      0 = 0 ∧
    centeredTransform
      (fun t => (SignedWeilCorrelation.realAutocorrelation (nymanCompletedTest n M hn v) t : ℂ))
      1 = 0 := by
  have hG := smoothSuperexponentialDecay_nymanCompletedTest n M hn hv ha hb
  have hp := centeredTransform_nymanCompletedTest_polar n M hn hv ha hb
  constructor
  · exact SignedWeilCorrelation.realAutocorrelation_transform_zero
      hG.decay hG.deriv.decay (hG.1.differentiable (by simp)) 0 hp.1 (by simpa using hp.2)
  · exact SignedWeilCorrelation.realAutocorrelation_transform_zero
      hG.decay hG.deriv.decay (hG.1.differentiable (by simp)) 1 hp.2 (by simpa using hp.1)

theorem realAutocorrelation_poleCancellation_nymanFullReturn_centeredTransform_zero
    (n : ℕ) [NeZero n] {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0)
    {s : ℂ} (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    centeredTransform
      (fun t => (SignedWeilCorrelation.realAutocorrelation
        (poleCancellationOperator (nymanFullReturn n u)) t : ℂ)) s = 0 := by
  have hG := (smoothSuperexponentialDecay_nymanFullReturn hu ha hb n).poleCancellationOperator
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at h1
  exact SignedWeilCorrelation.realAutocorrelation_transform_zero
    hG.decay hG.deriv.decay (hG.1.differentiable (by simp)) s
    (centeredTransform_poleCancellation_nymanFullReturn_zero n hu ha hb hs1 hz)
    (centeredTransform_poleCancellation_nymanFullReturn_zero n hu ha hb
      (one_sub_ne_one_of_re_pos h0) (riemannZeta_one_sub_eq_zero_of_strip hz h0 h1))

end RiemannResearch.RH
