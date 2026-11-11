import RiemannResearch.Analysis.ActualRationalAutocorrelation
import RiemannResearch.Analysis.ActualZeroIntegratedPairing

/-!
# Literal Dirichlet-quadratic S₁ remainder

The arithmetic ratio-aggregation bridge identifies F with |A|²−E and J₄ with
the actual off-diagonal rational autocorrelation sum. The analytic bridge then
bounds the actual multiplicity-weighted sampled square. Dividing by the actual
nonzero zero count gives the literal normalized quadratic Q_T−E.

The correction retains the exact gamma integral, both signed endpoints, and
the exact polynomial subtraction. Its asymptotic reduction to the manuscript's
prime-power matrix and elementary endpoint budgets is not claimed here.
The only quantitative S₁ hypotheses are the named energy and mode providers.
-/

noncomputable section
open MeasureTheory Zeta23
open scoped BigOperators
open RiemannResearch.Fourier
open RiemannResearch.Analysis.ActualRationalAutocorrelation
open RiemannResearch.Analysis.ActualIntegratedDiscrepancy
open RiemannResearch.Analysis.ActualZeroIntegratedPairing
open RiemannResearch.Analysis.SpectralDerivativePairing
open RiemannResearch.Analysis.IntegratedCountingPairing
open RiemannResearch.Analysis.DirichletMeanSquare

namespace RiemannResearch.Analysis.ActualDirichletS1Remainder

def energy (s : Finset ℕ) (a : ℕ → ℂ) : ℝ := ∑ n ∈ s, ‖a n‖ ^ 2

/-- Literal grouped off-diagonal J₄ of the actual integer support. -/
def autocorrelationFourthEnergy (s : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ q ∈ (rationalFrequencySupport s).erase 1,
    ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 4

variable {κ : Type} [Fintype κ]

def approximationBudget (total : ℝ) (errS : ℝ → ℝ)
    (d : κ → ℂ) (η : κ → ℝ) (errC : ℝ → κ → ℝ) (T : ℝ) : ℝ :=
  T * (total - ∑ i, ‖d i‖ ^ 2) + errS T +
    26 * ∑ i, ‖d i‖ ^ 2 / η i + 2 * ∑ i, ‖d i‖ * errC T i

/-- Every deterministic correction in the exact twice-integrated formula. -/
def integratedCorrection (C : ℝ) (s : Finset ℕ) (a : ℕ → ℂ)
    (d : κ → ℂ) (ν : κ → ℝ) (T : ℝ) : ℂ :=
  (∫ t in 0..T, (mu t : ℂ) * centeredPolynomial s a t) +
    boundary complexArgument (complexPrimitive C) (centeredPolynomial s a)
      (polynomial (derivativeCoeff (centeredCoefficient s a) (centeredFrequency s))
        (centeredFrequency s)) 0 T +
    ∫ t in 0..T, polynomial d ν t *
      polynomial (secondCoeff (centeredCoefficient s a) (centeredFrequency s))
        (centeredFrequency s) t

/-- The actual multiplicity-weighted quadratic divided by the actual zero count. -/
def normalizedQuadratic (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ActualDirichletPolynomialGram.sampledSquare T s a / (Ncount 0 T : ℂ)

/-- Actual sampled-square numerator, literal rational J₄, and proved 1/M² gap.
Only the named actual S₁ energy and mode-correlation providers remain. -/
theorem sampledSquare_remainder_sq_le
    (C total : ℝ) (errS : ℝ → ℝ)
    (d : κ → ℂ) (ν η : κ → ℝ) (errC : ℝ → κ → ℝ)
    (henergy : MeanSquareError C total errS)
    (hmodes : ModeCorrelationError C d ν errC)
    (hν : Function.Injective ν) (hη : ∀ i, 0 < η i)
    (hνsep : ∀ i j, i ≠ j → η i ≤ |ν i - ν j|)
    (s : Finset ℕ) (a : ℕ → ℂ) (M : ℕ) (hM : 0 < M)
    (hs0 : ∀ n ∈ s, 0 < n) (hsM : ∀ n ∈ s, n ≤ M)
    {T : ℝ} (hT : 2 ≤ T) :
    ‖ActualDirichletPolynomialGram.sampledSquare T s a -
      (Ncount 0 T : ℂ) * (energy s a : ℂ) -
      integratedCorrection C s a d ν T‖ ^ 2 ≤
    approximationBudget total errS d η errC T *
      ((T + 26 * (M : ℝ) ^ 2) * autocorrelationFourthEnergy s a) := by
  classical
  have hδ : 0 < 1 / (M : ℝ) ^ 2 := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  have h := actual_zero_remainder_sq_le C total errS d ν η errC
    henergy hmodes hν hη hνsep
    (centeredCoefficient s a) (centeredFrequency s) (1 / (M : ℝ) ^ 2) hδ
    (centeredFrequency_separation_of_height s M hs0 hsM) hT
  have hsample : ActualZeroOrdinate.sum T (fun ρ =>
      polynomial (centeredCoefficient s a) (centeredFrequency s) ρ.im) =
      ActualDirichletPolynomialGram.sampledSquare T s a -
        (Ncount 0 T : ℂ) * (energy s a : ℂ) :=
    actual_sum_centeredPolynomial T s a hs0
  have hzero : ActualZeroOrdinate.sum 0 (fun ρ =>
      polynomial (centeredCoefficient s a) (centeredFrequency s) ρ.im) = 0 :=
    actual_sum_centeredPolynomial_zero s a
  have hfourth : fourthEnergy (centeredCoefficient s a) (centeredFrequency s) =
      autocorrelationFourthEnergy s a := centered_fourth_energy_eq s a
  rw [hsample, hzero, sub_zero, hfourth] at h
  simp only [div_div_eq_mul_div, div_one] at h
  have heq : ActualDirichletPolynomialGram.sampledSquare T s a -
      (Ncount 0 T : ℂ) * (energy s a : ℂ) - integratedCorrection C s a d ν T =
      ActualDirichletPolynomialGram.sampledSquare T s a -
      (Ncount 0 T : ℂ) * (energy s a : ℂ) -
      (∫ t in 0..T, (mu t : ℂ) * centeredPolynomial s a t) -
      boundary complexArgument (complexPrimitive C) (centeredPolynomial s a)
        (polynomial (derivativeCoeff (centeredCoefficient s a) (centeredFrequency s))
          (centeredFrequency s)) 0 T -
      (∫ t in 0..T, polynomial d ν t *
        polynomial (secondCoeff (centeredCoefficient s a) (centeredFrequency s))
          (centeredFrequency s) t) := by
    unfold integratedCorrection
    ring
  rw [heq]
  exact h

/-- Literal Q_T−E estimate after normalization by the actual nonzero count. -/
theorem normalizedQuadratic_remainder_sq_le
    (C total : ℝ) (errS : ℝ → ℝ)
    (d : κ → ℂ) (ν η : κ → ℝ) (errC : ℝ → κ → ℝ)
    (henergy : MeanSquareError C total errS)
    (hmodes : ModeCorrelationError C d ν errC)
    (hν : Function.Injective ν) (hη : ∀ i, 0 < η i)
    (hνsep : ∀ i j, i ≠ j → η i ≤ |ν i - ν j|)
    (s : Finset ℕ) (a : ℕ → ℂ) (M : ℕ) (hM : 0 < M)
    (hs0 : ∀ n ∈ s, 0 < n) (hsM : ∀ n ∈ s, n ≤ M)
    {T : ℝ} (hT : 2 ≤ T) (hN : Ncount 0 T ≠ 0) :
    ‖normalizedQuadratic T s a - (energy s a : ℂ) -
      integratedCorrection C s a d ν T / (Ncount 0 T : ℂ)‖ ^ 2 ≤
      approximationBudget total errS d η errC T *
        ((T + 26 * (M : ℝ) ^ 2) * autocorrelationFourthEnergy s a) /
          (Ncount 0 T : ℝ) ^ 2 := by
  have hnum := sampledSquare_remainder_sq_le C total errS d ν η errC
    henergy hmodes hν hη hνsep s a M hM hs0 hsM hT
  have hnC : (Ncount 0 T : ℂ) ≠ 0 := by exact_mod_cast hN
  have heq : normalizedQuadratic T s a - (energy s a : ℂ) -
      integratedCorrection C s a d ν T / (Ncount 0 T : ℂ) =
      (ActualDirichletPolynomialGram.sampledSquare T s a -
        (Ncount 0 T : ℂ) * (energy s a : ℂ) -
        integratedCorrection C s a d ν T) / (Ncount 0 T : ℂ) := by
    unfold normalizedQuadratic
    field_simp [hnC]
  rw [heq, norm_div, div_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hnum (sq_nonneg _)

end RiemannResearch.Analysis.ActualDirichletS1Remainder
