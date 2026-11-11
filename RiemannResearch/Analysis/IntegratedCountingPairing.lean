import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring

/-!
# Signed twice-integrated counting pairings

This is the exact analytic identity in Section 2, equation (7), of
`FRZ_Strengthening_2026-11-10`. Both endpoints and their signs are retained.
Only right derivatives in the open interval are required: the primitive of
a counting discrepancy need not be differentiable at a jump of that discrepancy.

The identification of `abelPairing` with a sum over actual zeta zeros, and the
classical mean-square theorem for the actual normalized S₁, are separate inputs.
No assertion about either is made in this module.

Analytic source: the ordinary integration-by-parts identity, as used for S₁ in
R. P. Brent, D. J. Platt and T. S. Trudgian, "Accurate estimation of sums over
zeros of the Riemann zeta-function", Math. Comp. 90 (2021), 2923–2935.
-/

noncomputable section
open MeasureTheory

namespace RiemannResearch.Analysis.IntegratedCountingPairing

/-- The Abel–Stieltjes pairing, with its actual boundary convention. -/
def abelPairing (N F F₁ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  N b * F b - N a * F a - ∫ t in a..b, N t * F₁ t

/-- Both signed boundary terms produced by two integrations by parts. -/
def boundary (S U F F₁ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  S b * F b - S a * F a - (U b * F₁ b - U a * F₁ a)

/-- Exact signed formula for a counting function decomposed as `N = M + S`,
where `M' = m`, `U' = S`, and `F' = F₁`, `F₁' = F₂`.
Right derivatives suffice even when S has jumps. -/
theorem abelPairing_eq_twice_integrated
    {a b : ℝ} {M m S U F F₁ F₂ : ℝ → ℂ}
    (hM : ContinuousOn M (Set.uIcc a b))
    (hU : ContinuousOn U (Set.uIcc a b))
    (hF : ContinuousOn F (Set.uIcc a b))
    (hF₁ : ContinuousOn F₁ (Set.uIcc a b))
    (hMm : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt M (m t) (Set.Ioi t) t)
    (hUS : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt U (S t) (Set.Ioi t) t)
    (hFF₁ : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt F (F₁ t) (Set.Ioi t) t)
    (hF₁F₂ : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt F₁ (F₂ t) (Set.Ioi t) t)
    (hm : IntervalIntegrable m volume a b)
    (hS : IntervalIntegrable S volume a b)
    (hF₁i : IntervalIntegrable F₁ volume a b)
    (hF₂i : IntervalIntegrable F₂ volume a b) :
    abelPairing (fun t => M t + S t) F F₁ a b =
      (∫ t in a..b, m t * F t) + boundary S U F F₁ a b +
        ∫ t in a..b, U t * F₂ t := by
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hM hF hMm hFF₁ hm hF₁i
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hU hF₁ hUS hF₁F₂ hS hF₂i
  have hprod : IntervalIntegrable (fun t => M t * F₁ t) volume a b :=
    (hM.mul hF₁).intervalIntegrable
  unfold abelPairing boundary
  simp only [add_mul]
  rw [intervalIntegral.integral_add hprod
    (hS.mul_continuousOn hF₁), hfirst, hsecond]
  ring

/-- Exact subtraction of any continuous spectral approximation P.
The residual remains a signed integral rather than a sum of entrywise errors. -/
theorem integral_subtraction_identity
    {a b : ℝ} {U P F₂ : ℝ → ℂ}
    (hU : ContinuousOn U (Set.uIcc a b))
    (hP : ContinuousOn P (Set.uIcc a b))
    (hF₂ : IntervalIntegrable F₂ volume a b) :
    (∫ t in a..b, U t * F₂ t) =
      (∫ t in a..b, P t * F₂ t) +
        ∫ t in a..b, (U t - P t) * F₂ t := by
  have hu := hF₂.continuousOn_mul hU
  have hp := hF₂.continuousOn_mul hP
  simp only [sub_mul]
  rw [intervalIntegral.integral_sub hu hp]
  ring

end RiemannResearch.Analysis.IntegratedCountingPairing
