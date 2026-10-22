import RiemannResearch.RH.NymanTransformNullity
import RiemannResearch.RH.NymanCompletionAdmissibility

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual remote tail retains the exact negative spectral signature

Source: user-provided argument, equations (9.3), (10.3). The support, smooth
admissibility, transform factorization, and integrability providers concern the
actual arithmetic completion. Integral subtraction is therefore justified,
rather than assuming a transform-signature condition on an abstract tail.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis

namespace MeasureTheory.BilateralLaplace

theorem centeredTransform_sub {f g : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hg : HasExponentialMoments g) (s : ℂ) :
    centeredTransform (f - g) s = centeredTransform f s - centeredTransform g s := by
  change (∫ y : ℝ, (f y - g y) * kernel (s - 1 / 2) y) = _
  simp only [sub_mul]
  exact integral_sub (integrable_integrand hf (s - 1 / 2))
    (integrable_integrand hg (s - 1 / 2))

end MeasureTheory.BilateralLaplace

namespace RiemannResearch.RH

open ZetaConductorRegularization

theorem centeredTransform_poleCancellation_of_smoothSuperexponential
    {f : ℝ → ℂ} (hf : SmoothSuperexponentialDecay f) (s : ℂ) :
    centeredTransform (poleCancellationOperator f) s =
      s * (s - 1) * centeredTransform f s :=
  hf.decay.centeredTransform_poleCancellationOperator hf.deriv.decay hf.deriv.deriv.decay
    (hf.1.differentiable (by simp)) (hf.deriv.1.differentiable (by simp))
    hf.deriv.deriv.1.continuous s

/-- Actual integral subtraction for the arithmetic tail, with both input
integrability hypotheses discharged by proved smooth admissibility. -/
theorem centeredTransform_nymanCompletionTail_sub (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) (s : ℂ) :
    centeredTransform (nymanCompletionTail n M hn v) s =
      centeredTransform (nymanCompletedTest n M hn v) s -
        centeredTransform (poleCancellationOperator v) s := by
  have hG := smoothSuperexponentialDecay_nymanCompletedTest n M hn hv ha hb
  have hf := (smoothSuperexponentialDecay_of_compact_interval hv ha hb).poleCancellationOperator
  exact centeredTransform_sub (hG.decay.hasExponentialMoments hG.1.continuous)
    (hf.decay.hasExponentialMoments hf.1.continuous) s

/-- Exact entire transform of the actual remote tail, including every arithmetic
completion coefficient through its finite inverse potential. -/
theorem centeredTransform_nymanCompletionTail (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) (s : ℂ) :
    centeredTransform (nymanCompletionTail n M hn v) s =
      s * (s - 1) * (conductorZeta n s *
        centeredTransform (nymanInversePotential n M hn v) s - centeredTransform v s) := by
  rw [centeredTransform_nymanCompletionTail_sub n M hn hv ha hb s,
    centeredTransform_nymanCompletedTest n M hn hv ha hb s,
    centeredTransform_poleCancellation_of_smoothSuperexponential
      (smoothSuperexponentialDecay_of_compact_interval hv ha hb) s]
  ring

/-- The signature used by the off-line-zero tail lower bound now follows for
the concrete tail; it is not an assumed interpolation constraint. -/
theorem centeredTransform_nymanCompletionTail_zeta_signature (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s = 0) :
    centeredTransform (nymanCompletionTail n M hn v) s =
      -centeredTransform (poleCancellationOperator v) s := by
  rw [centeredTransform_nymanCompletionTail_sub n M hn hv ha hb s,
    centeredTransform_nymanCompletedTest_zero n M hn hv ha hb hs hz, zero_sub]

/-- Both polar moments of the actual remote tail vanish. -/
theorem centeredTransform_nymanCompletionTail_polar (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    centeredTransform (nymanCompletionTail n M hn v) 0 = 0 ∧
      centeredTransform (nymanCompletionTail n M hn v) 1 = 0 := by
  constructor <;> simp [centeredTransform_nymanCompletionTail n M hn hv ha hb]

end RiemannResearch.RH
