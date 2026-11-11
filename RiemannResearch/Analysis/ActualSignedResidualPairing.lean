import RiemannResearch.Analysis.SpectralSignedTail
import RiemannResearch.Analysis.ActualZeroIntegratedPairing

/-!
# Actual zero remainder with its exact combined signed defect

This consumer preserves the analytic zero multiplicities, the exact gamma
integral, and both signed endpoints from ActualZeroIntegratedPairing.
It does not assume the classical S₁ energy or individual-mode providers.
Its bound contains the actual signed defect; proving a small quantitative
bound for that defect remains a separate analytic obligation.

Source: the exact FRZ residual identity and the November 11 investigation.
-/

noncomputable section
open MeasureTheory Zeta23
open scoped BigOperators
open RiemannResearch.Analysis.ActualZeroDiscrepancy
open RiemannResearch.Analysis.ActualIntegratedDiscrepancy
open RiemannResearch.Analysis.ActualZeroIntegratedPairing
open RiemannResearch.Analysis.IntegratedCountingPairing
open RiemannResearch.Analysis.DirichletMeanSquare
open RiemannResearch.Analysis.SpectralResidualMeanSquare
open RiemannResearch.Analysis.SpectralDerivativePairing
open RiemannResearch.Analysis.ZeroOrdinate

namespace RiemannResearch.Analysis.ActualSignedResidualPairing


/-- A single actual ordinate mode, with exact gamma and endpoint corrections. -/
theorem actual_mode_pairing_mul_sq (C ω : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ((ω : ℂ) ^ 2) * (∫ t in 0..T, complexPrimitive C t * phase ω t) =
      (∫ t in 0..T, (mu t : ℂ) * phase ω t) +
      boundary complexArgument (complexPrimitive C) (phase ω)
        (fun t => ((ω : ℂ) * Complex.I) * phase ω t) 0 T -
      ActualZeroOrdinate.sum T (fun ρ => phase ω ρ.im) +
      ActualZeroOrdinate.sum 0 (fun ρ => phase ω ρ.im) := by
  have h := actual_sum_sub_eq_twice_integrated le_rfl hT C
    (fun _ : Unit => (1 : ℂ)) (fun _ : Unit => ω)
  simp only [boundary, polynomial, derivativeCoeff, secondCoeff, Fintype.sum_unique,
    one_mul, mul_one] at h ⊢
  have hi : (∫ t in 0..T, complexPrimitive C t *
      (-((ω : ℂ) ^ 2) * phase ω t)) =
      -((ω : ℂ) ^ 2) * ∫ t in 0..T, complexPrimitive C t * phase ω t := by
    simp_rw [show ∀ t, complexPrimitive C t * (-((ω : ℂ) ^ 2) * phase ω t) =
      -((ω : ℂ) ^ 2) * (complexPrimitive C t * phase ω t) by intro t; ring]
    rw [intervalIntegral.integral_const_mul]
  rw [hi] at h
  linear_combination h

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- No unproved asymptotic provider: the signed defect itself remains visible. -/
theorem actual_zero_remainder_sq_le_exact_signedDefect
    (C total : ℝ) (d : κ → ℂ) (ν : κ → ℝ)
    (c : ι → ℂ) (ω : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ |ω i - ω j|)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖ActualZeroOrdinate.sum T (fun ρ => polynomial c ω ρ.im) -
      ActualZeroOrdinate.sum 0 (fun ρ => polynomial c ω ρ.im) -
      (∫ t in 0..T, (mu t : ℂ) * polynomial c ω t) -
      boundary complexArgument (complexPrimitive C)
        (polynomial c ω) (polynomial (derivativeCoeff c ω) ω) 0 T -
      (∫ t in 0..T, polynomial d ν t * polynomial (secondCoeff c ω) ω t)‖ ^ 2 ≤
      (T * (total - ∑ i, ‖d i‖ ^ 2) +
        signedDefect (complexPrimitive C) d (fun i => phase (ν i)) T total
          (volume.restrict (Set.Ioc 0 T))) *
        ((T + 26 / δ) * fourthEnergy c ω) := by
  classical
  rw [actual_remainder_eq_residual le_rfl hT C c ω
    (polynomial d ν) (polynomial_continuous d ν)]
  have he (i : κ) : MemLp (phase (ν i)) 2 (volume.restrict (Set.Ioc 0 T)) := by
    have hc : Continuous (phase (ν i)) := by unfold phase; fun_prop
    exact MemLp.of_bound hc.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun t => (phase_norm (ν i) t).le))
  have hid := integral_residual_eq_tail_add_signedDefect
    (complexPrimitive_memLp C 0 T) d he T total
  have hR : (∫ t in 0..T, ‖complexPrimitive C t - polynomial d ν t‖ ^ 2) ≤
      T * (total - ∑ i, ‖d i‖ ^ 2) +
        signedDefect (complexPrimitive C) d (fun i => phase (ν i)) T total
          (volume.restrict (Set.Ioc 0 T)) := by
    rw [intervalIntegral.integral_of_le hT]
    exact hid.le
  simpa only [sub_zero] using
    residual_second_derivative_pairing_sq_le_uniform hT
      (complexPrimitive_memLp C 0 T) (polynomial_memLp d ν 0 T) hR c ω δ hδ hsep

end RiemannResearch.Analysis.ActualSignedResidualPairing
