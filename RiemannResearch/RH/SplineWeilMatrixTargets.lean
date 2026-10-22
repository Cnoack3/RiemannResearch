import RiemannResearch.RH.FixedWidthWeilDiscrepancy
import RiemannResearch.RH.WeilSpectralPairing
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card

/-!
# Actual dyadic spline Weil matrices and polynomial-loss targets

Source: user-provided layer-cake continuation, Sections 29 and 32--40.
The basis, arithmetic matrix entries, mass, and positive difference energy
below are literal functions and integrals for the stated dyadic mesh.

`SplineEnergyAdmissibility`, `SplineQuadraticRepresentation`, and
`SplineWeilHermitian` are OPEN analytic provider propositions. In particular,
the existing smooth-test pairing theorem does not automatically apply to
piecewise-linear hats. Defining these propositions does not prove them.
The polynomial lower bounds are the unresolved RH research targets.

The real Bochner integrals and arithmetic sums are totalized. Nonnegativity
alone does not certify their integrability; the admissibility proposition
records that separate obligation. No RH theorem is asserted in this module.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open RiemannResearch.Analysis
open RiemannResearch.RH.SignedWeilCorrelation
open RiemannResearch.RH.FixedWidthWeilDiscrepancy

namespace RiemannResearch.RH.SplineWeilMatrixTargets

def splineMesh (j : ℕ) : ℝ := Real.log 2 / (2 : ℝ) ^ j

theorem splineMesh_pos (j : ℕ) : 0 < splineMesh j := by
  exact div_pos (Real.log_pos (by norm_num)) (pow_pos (by norm_num) j)

def splineDimension (j : ℕ) : ℕ := 2 * j * 2 ^ j - 1

abbrev SplineIndex (j : ℕ) := Fin (splineDimension j)

theorem card_splineIndex (j : ℕ) :
    Fintype.card (SplineIndex j) = 2 * j * 2 ^ j - 1 := by
  exact Fintype.card_fin _

/-- Increasing indices enumerate the interior centers from
`(-j*2^j+1)*h_j` to `(j*2^j-1)*h_j`. -/
def splineCenter (j : ℕ) (i : SplineIndex j) : ℝ :=
  ((i.val : ℝ) + 1 - ((j * 2 ^ j : ℕ) : ℝ)) * splineMesh j

def splineBasis (j : ℕ) (i : SplineIndex j) (x : ℝ) : ℂ :=
  (centeredHat (splineMesh j) (x - splineCenter j i) : ℂ)

def splineTest (j : ℕ) (c : SplineIndex j → ℂ) (x : ℝ) : ℂ :=
  ∑ i, c i * splineBasis j i x

@[simp] theorem splineTest_zero (j : ℕ) :
    splineTest j (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [splineTest]

def splineMass (f : ℝ → ℂ) : ℝ := ∫ x : ℝ, ‖f x‖ ^ 2

def differenceMass (f : ℝ → ℂ) (u : ℝ) : ℝ :=
  ∫ x : ℝ, ‖f x - f (x - u)‖ ^ 2

/-- The actual archimedean difference energy with
`k(u)=exp(-u/2)/(1-exp(-2u))` on the positive half-line. -/
def positiveDifferenceEnergy (f : ℝ → ℂ) : ℝ :=
  ∫ u : ℝ, weilGammaKernel u * differenceMass f u ∂positiveMeasure

def splineEnergy (f : ℝ → ℂ) : ℝ :=
  splineMass f + positiveDifferenceEnergy f

theorem splineMass_nonneg (f : ℝ → ℂ) : 0 ≤ splineMass f := by
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem differenceMass_nonneg (f : ℝ → ℂ) (u : ℝ) :
    0 ≤ differenceMass f u := by
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem positiveDifferenceEnergy_nonneg (f : ℝ → ℂ) :
    0 ≤ positiveDifferenceEnergy f := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (weilGammaKernel_nonneg (show 0 < u from hu))
    (differenceMass_nonneg f u)

theorem splineMass_le_splineEnergy (f : ℝ → ℂ) :
    splineMass f ≤ splineEnergy f := by
  exact le_add_of_nonneg_right (positiveDifferenceEnergy_nonneg f)

theorem splineEnergy_nonneg (f : ℝ → ℂ) : 0 ≤ splineEnergy f :=
  (splineMass_nonneg f).trans (splineMass_le_splineEnergy f)

@[simp] theorem splineMass_zero : splineMass (fun _ => 0) = 0 := by
  simp [splineMass]

@[simp] theorem differenceMass_zero (u : ℝ) :
    differenceMass (fun _ => 0) u = 0 := by
  simp [differenceMass]

@[simp] theorem splineEnergy_zero : splineEnergy (fun _ => 0) = 0 := by
  simp [splineEnergy, positiveDifferenceEnergy]

/-- OPEN: finiteness of all three actual integrals used for spline energy.
This is separate from the unconditional signs of their totalized values. -/
def SplineEnergyAdmissibility : Prop :=
  ∀ j (c : SplineIndex j → ℂ),
    Integrable (fun x : ℝ => ‖splineTest j c x‖ ^ 2) ∧
    (∀ u : ℝ, Integrable
      (fun x : ℝ => ‖splineTest j c x - splineTest j c (x - u)‖ ^ 2)) ∧
    Integrable (fun u : ℝ => weilGammaKernel u * differenceMass (splineTest j c) u)
      positiveMeasure

/-- Entries retain the actual complete signed arithmetic pairing. -/
def splineWeilMatrix (j : ℕ) : Matrix (SplineIndex j) (SplineIndex j) ℂ :=
  fun i k => arithmeticWeilPairing (splineBasis j i) (splineBasis j k)

def splineMatrixQuadratic (j : ℕ) (c : SplineIndex j → ℂ) : ℝ :=
  (∑ i, ∑ k, conj (c i) * splineWeilMatrix j i k * c k).re

/-- OPEN: finite expansion of the completed arithmetic form on the actual
nonsmooth hats. Required admissibility and finite-sum interchanges must be
proved; they are not supplied by the definition of the pairing. -/
def SplineQuadraticRepresentation : Prop :=
  ∀ j (c : SplineIndex j → ℂ),
    completedWeilForm (splineTest j c) = splineMatrixQuadratic j c

/-- OPEN: extension of Hermitian symmetry to the actual hat basis. -/
def SplineWeilHermitian : Prop :=
  ∀ j (i k : SplineIndex j),
    splineWeilMatrix j i k = conj (splineWeilMatrix j k i)

/-- OPEN RH target: one polynomial tolerance works for all sufficiently
large actual spline spaces, with the complete signed arithmetic form. -/
def PolynomialSplineEnergyLowerBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ, ∃ j₀ : ℕ, ∀ j, j₀ ≤ j →
    ∀ c : SplineIndex j → ℂ,
      -(C * (1 + (j : ℝ)) ^ A) * splineEnergy (splineTest j c) ≤
        completedWeilForm (splineTest j c)

/-- The stronger mass-normalized polynomial target from the same program. -/
def PolynomialSplineMassLowerBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ, ∃ j₀ : ℕ, ∀ j, j₀ ≤ j →
    ∀ c : SplineIndex j → ℂ,
      -(C * (1 + (j : ℝ)) ^ A) * splineMass (splineTest j c) ≤
        completedWeilForm (splineTest j c)

theorem PolynomialSplineMassLowerBound.to_energy
    (h : PolynomialSplineMassLowerBound) : PolynomialSplineEnergyLowerBound := by
  obtain ⟨C, hC, A, j₀, hbound⟩ := h
  refine ⟨C, hC, A, j₀, ?_⟩
  intro j hj c
  have hp : 0 ≤ C * (1 + (j : ℝ)) ^ A := by positivity
  have hm := mul_le_mul_of_nonneg_left (splineMass_le_splineEnergy (splineTest j c)) hp
  have hl := hbound j hj c
  nlinarith

/-- Quantitative interpolation transfer for the actual arithmetic forms.
The approximation error and energy bound are explicit hypotheses, so an
unproved density or rate estimate is never silently used. -/
theorem completedWeilForm_lower_of_spline_approximation
    (j : ℕ) (c : SplineIndex j → ℂ) (f : ℝ → ℂ)
    (τ B η : ℝ) (hτ : 0 ≤ τ)
    (hlower : -τ * splineEnergy (splineTest j c) ≤
      completedWeilForm (splineTest j c))
    (henergy : splineEnergy (splineTest j c) ≤ B)
    (herror : |completedWeilForm (splineTest j c) - completedWeilForm f| ≤ η) :
    -τ * B - η ≤ completedWeilForm f := by
  have hm := mul_le_mul_of_nonneg_left henergy hτ
  have he := (abs_le.mp herror).2
  nlinarith

end RiemannResearch.RH.SplineWeilMatrixTargets
