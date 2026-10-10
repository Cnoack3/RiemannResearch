import RiemannResearch.Analysis.LogarithmicPrefixMellin
import RiemannResearch.Analysis.ActualAnnularContinuity
import RiemannResearch.RH.AnnularMellinContinuation
import RiemannResearch.RH.AnnularCriticalEnergyTransfer

/-!
# Actual all-cutoff annular energy implies RH

The logarithmic critical-energy bound supplies all positively damped
weighted memberships. The actual Mellin continuation then excludes every
zero to the right of 1/2. No ActualRHEnergyCriterion, local identity provider,
model asymptotic, or simplicity assumption is used. The actual energy bound
and signed-residual estimate remain open arithmetic hypotheses.

Source: the classical weighted-energy/meromorphic-pole argument, applied to
the actual annular signal using the proved initial Mellin identity.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH.AnnularEnergyRH
open MeasureTheory.WeightedMellin
open RiemannResearch.Analysis.WeightedMellinTopology
open RiemannResearch.Analysis.SignedLatticeEnergy
open RiemannResearch.RH.AnnularPrimePair
open RiemannResearch.RH.AnnularCriticalEnergy
open RiemannResearch.RH.AnnularMellinContinuation

theorem actualAnnular_prefix_eq_criticalEnergy {X : ℝ} (hX : 1 ≤ X) :
    (∫ x in (1 : ℝ)..X, ‖actualAnnularVector x‖ ^ 2 * x ^ (-2 : ℝ)) =
      criticalEnergy actualPrimeSignal X := by
  rw [intervalIntegral.integral_of_le hX, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  simp only [actualAnnularVector, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.rpow_neg hx0.le, Real.rpow_ofNat, div_eq_mul_inv]

theorem actualAnnular_Ha_of_primeEnergyUpperBound
    (henergy : ActualPrimeEnergyUpperBound) {a : ℝ} (ha : (1 / 2 : ℝ) < a) :
    Ha a actualAnnularVector := by
  obtain ⟨C, hC⟩ := henergy
  apply finiteEnergy_of_logarithmic_prefix actualAnnularVector
    actualAnnularVector_measurable actualAnnularVector_continuous.continuousOn
    (max C 0) (le_max_right C 0) ?_ (2 * a) (by linarith)
  intro X hX
  rw [actualAnnular_prefix_eq_criticalEnergy (by linarith)]
  exact (hC X hX).trans (mul_le_mul_of_nonneg_right (le_max_left C 0)
    (Real.log_nonneg (by linarith)))

/-- Conditional only on the stated actual arithmetic bound. This removes
the separate analytic RH-energy criterion from the sufficient direction. -/
theorem riemannHypothesis_of_actualPrimeEnergyUpperBound
    (henergy : ActualPrimeEnergyUpperBound) : RiemannHypothesis :=
  riemannHypothesis_of_actualAnnular_all_damping
    (fun _ ha => actualAnnular_Ha_of_primeEnergyUpperBound henergy ha)

theorem riemannHypothesis_of_actualEnergyUpperBound
    (henergy : ActualEnergyUpperBound) : RiemannHypothesis :=
  riemannHypothesis_of_actualPrimeEnergyUpperBound
    (actualPrimeEnergyUpperBound_iff_actualEnergyUpperBound.mpr henergy)

/-- The singular-series model estimate remains an explicit independent
arithmetic premise. The analytic RH-energy provider has been removed. -/
theorem riemannHypothesis_of_actualSignedResidualUpperBound
    (hmodel : ActualModelLogBound) (hresidual : ActualSignedResidualUpperBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_actualEnergyUpperBound
    ((actualEnergyUpperBound_iff_signedResidualUpperBound hmodel).mpr hresidual)

end RiemannResearch.RH.AnnularEnergyRH
