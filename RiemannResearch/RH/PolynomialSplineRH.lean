import RiemannResearch.RH.SplineWeilMatrixTargets
import RiemannResearch.RH.PolynomialWeilCriterion

/-!
# Conditional finite-spline polynomial-loss route to RH

Source: user-provided layer-cake continuation, Theorem 38.2.
The quantitative interpolation interface records actual approximation errors,
energies, and the conversion of level weights to separation weights. It is
not proved here. Together with the two-hat identity, Landau detection, and
the polynomial spline lower bound, it yields Mathlib's actual RH.

All four substantive providers remain explicit. In particular, neither a
fixed-vector limit nor decreasing errors are used to handle a growing
polynomial tolerance. The ordinary proof of the quantitative interface is
archived in section 38.2 of LayerCakeSublevelProgram20260918.md.
-/

namespace RiemannResearch.RH.SplineWeilMatrixTargets

open FixedWidthWeilDiscrepancy

/-- OPEN quantitative interpolation provider. For every degree and starting
level, actual spline approximants to the fixed-width two-hat tests have
bounded reference energy and sufficiently small complete-form error. -/
def QuantitativeTwoHatSplineApproximation (h : ℝ) : Prop :=
  ∀ (A j₀ : ℕ), ∃ B : ℝ, 0 ≤ B ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∃ E : ℝ, 0 ≤ E ∧ ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      ∃ j : ℕ, ∃ c : SplineIndex j → ℂ,
        j₀ ≤ j ∧ (1 + (j : ℝ)) ^ A ≤ K * (1 + x) ^ A ∧
        splineEnergy (splineTest j c) ≤ B ∧
        |completedWeilForm (splineTest j c) - completedWeilForm (twoHatTest h x)| ≤
          E * (1 + x) ^ A

/-- Conditional research reduction for the actual finite spline test spaces.
It constructs the polynomial lower bound on the two-hat family from the
quantified approximation data rather than assuming the desired implication. -/
theorem riemannHypothesis_of_polynomial_spline_energy
    (h : ℝ) (hidentity : TwoHatWeilIdentity h)
    (hdetect : FixedWidthLandauDetection h)
    (happrox : QuantitativeTwoHatSplineApproximation h)
    (hpoly : PolynomialSplineEnergyLowerBound) : RiemannHypothesis := by
  obtain ⟨C, hC, A, j₀, hbound⟩ := hpoly
  obtain ⟨B, hB, K, hK, E, hE, R, hinterp⟩ := happrox A j₀
  apply riemannHypothesis_of_twoHat_polynomial_lower h hidentity hdetect
    (C * K * B + E) (by positivity) A (max R 0)
  intro x hx
  have hxR : R ≤ x := (le_max_left _ _).trans hx
  obtain ⟨j, c, hj, hweight, henergy, herror⟩ := hinterp x hxR
  have hτ : 0 ≤ C * (1 + (j : ℝ)) ^ A := by positivity
  have hl := completedWeilForm_lower_of_spline_approximation j c (twoHatTest h x)
    (C * (1 + (j : ℝ)) ^ A) B (E * (1 + x) ^ A) hτ
    (hbound j hj c) henergy herror
  have hm := mul_le_mul_of_nonneg_left hweight (mul_nonneg hC hB)
  nlinarith

/-- The mass-normalized target is stronger and supplies the same conditional
RH conclusion through the proved mass-to-energy comparison. -/
theorem riemannHypothesis_of_polynomial_spline_mass
    (h : ℝ) (hidentity : TwoHatWeilIdentity h)
    (hdetect : FixedWidthLandauDetection h)
    (happrox : QuantitativeTwoHatSplineApproximation h)
    (hpoly : PolynomialSplineMassLowerBound) : RiemannHypothesis :=
  riemannHypothesis_of_polynomial_spline_energy h hidentity hdetect happrox hpoly.to_energy

/-- The matrix target uses the literal full signed Weil entries. -/
def PolynomialSplineMatrixEnergyLowerBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ, ∃ j₀ : ℕ, ∀ j, j₀ ≤ j →
    ∀ c : SplineIndex j → ℂ,
      -(C * (1 + (j : ℝ)) ^ A) * splineEnergy (splineTest j c) ≤
        splineMatrixQuadratic j c

theorem PolynomialSplineMatrixEnergyLowerBound.to_form
    (hrep : SplineQuadraticRepresentation)
    (h : PolynomialSplineMatrixEnergyLowerBound) : PolynomialSplineEnergyLowerBound := by
  obtain ⟨C, hC, A, j₀, hbound⟩ := h
  refine ⟨C, hC, A, j₀, ?_⟩
  intro j hj c
  rw [hrep j c]
  exact hbound j hj c

/-- Native actual-matrix version. The nonsmooth hat representation is an
additional explicit analytic provider; no such representation is postulated. -/
theorem riemannHypothesis_of_polynomial_spline_matrix
    (h : ℝ) (hidentity : TwoHatWeilIdentity h)
    (hdetect : FixedWidthLandauDetection h)
    (happrox : QuantitativeTwoHatSplineApproximation h)
    (hrep : SplineQuadraticRepresentation)
    (hpoly : PolynomialSplineMatrixEnergyLowerBound) : RiemannHypothesis :=
  riemannHypothesis_of_polynomial_spline_energy h hidentity hdetect happrox
    (hpoly.to_form hrep)

end RiemannResearch.RH.SplineWeilMatrixTargets
