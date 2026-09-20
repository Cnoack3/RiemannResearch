import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Finite projection determinantal probability measures

For `n` feature functions `ψ`, the labeled finite projection law has density
`‖det (ψ i (x j))‖² / n!` relative to the product base measure.  This module
constructs that measure, proves that determinant normalization makes it a
probability measure, and proves that its configurations are almost surely simple.
The normalization is discharged for orthonormal features in
`ContinuousProjectionDensity`.

Source: the finite-rank projection construction in Hough, Krishnapur, Peres,
and Virág, *Determinantal Processes and Independence*, Probability Surveys 3
(2006), Section 2, https://doi.org/10.1214/154957806000000078.  The source supports
the density construction and terminology; the proofs below are direct.
-/

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace ProbabilityTheory.ContinuousProjectionDPP

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- The feature matrix at a labeled configuration: features are rows. -/
def evalMatrix (ψ : Fin n → X → ℂ) (x : Fin n → X) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ψ i (x j)

/-- The squared Slater determinant. -/
def squaredDet (ψ : Fin n → X → ℂ) (x : Fin n → X) : ℝ :=
  ‖(evalMatrix ψ x).det‖ ^ 2

/-- The real-valued joint density of the labeled projection process. -/
def density (ψ : Fin n → X → ℂ) (x : Fin n → X) : ℝ :=
  squaredDet ψ x / (n.factorial : ℝ)

/-- The finite projection law, defined as an actual measure. -/
def law (μ : Measure X) (ψ : Fin n → X → ℂ) : Measure (Fin n → X) :=
  (Measure.pi fun _ : Fin n => μ).withDensity (fun x => ENNReal.ofReal (density ψ x))

lemma squaredDet_nonneg (ψ : Fin n → X → ℂ) (x : Fin n → X) :
    0 ≤ squaredDet ψ x := sq_nonneg _

lemma density_nonneg (ψ : Fin n → X → ℂ) (x : Fin n → X) :
    0 ≤ density ψ x := div_nonneg (squaredDet_nonneg ψ x) (Nat.cast_nonneg _)

lemma integrable_density {μ : Measure X} {ψ : Fin n → X → ℂ}
    (h : Integrable (squaredDet ψ) (Measure.pi fun _ : Fin n => μ)) :
    Integrable (density ψ) (Measure.pi fun _ : Fin n => μ) :=
  h.div_const _

lemma integral_density_eq_one {μ : Measure X} {ψ : Fin n → X → ℂ}
    (h : (∫ x, squaredDet ψ x ∂(Measure.pi fun _ : Fin n => μ)) = n.factorial) :
    (∫ x, density ψ x ∂(Measure.pi fun _ : Fin n => μ)) = 1 := by
  simp only [density, integral_div, h]
  exact div_self (by exact_mod_cast n.factorial_ne_zero)

lemma lintegral_density_eq_one {μ : Measure X} {ψ : Fin n → X → ℂ}
    (hi : Integrable (squaredDet ψ) (Measure.pi fun _ : Fin n => μ))
    (hn : (∫ x, squaredDet ψ x ∂(Measure.pi fun _ : Fin n => μ)) = n.factorial) :
    (∫⁻ x, ENNReal.ofReal (density ψ x) ∂(Measure.pi fun _ : Fin n => μ)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_density hi)
    (Filter.Eventually.of_forall (density_nonneg ψ)), integral_density_eq_one hn]
  simp

/-- Determinant normalization turns the Slater measure into a probability law. -/
theorem isProbabilityMeasure_law {μ : Measure X} {ψ : Fin n → X → ℂ}
    (hi : Integrable (squaredDet ψ) (Measure.pi fun _ : Fin n => μ))
    (hn : (∫ x, squaredDet ψ x ∂(Measure.pi fun _ : Fin n => μ)) = n.factorial) :
    IsProbabilityMeasure (law μ ψ) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_density_eq_one hi hn

lemma squaredDet_eq_zero_of_collision (ψ : Fin n → X → ℂ) (x : Fin n → X)
    {i j : Fin n} (hne : i ≠ j) (hij : x i = x j) : squaredDet ψ x = 0 := by
  have hd : (evalMatrix ψ x).det = 0 :=
    Matrix.det_zero_of_column_eq hne (fun k => congrArg (ψ k) hij)
  simp [squaredDet, hd]

lemma density_eq_zero_of_collision (ψ : Fin n → X → ℂ) (x : Fin n → X)
    {i j : Fin n} (hne : i ≠ j) (hij : x i = x j) : density ψ x = 0 := by
  simp [density, squaredDet_eq_zero_of_collision ψ x hne hij]

/-- Repeated positions have zero density, so the law is simple.  This does not
require a nonatomic base measure. -/
theorem ae_injective_law {μ : Measure X} {ψ : Fin n → X → ℂ}
    (hi : Integrable (squaredDet ψ) (Measure.pi fun _ : Fin n => μ)) :
    ∀ᵐ x ∂law μ ψ, Function.Injective x := by
  rw [law, ae_withDensity_iff' (integrable_density hi).aemeasurable.ennreal_ofReal]
  exact Filter.Eventually.of_forall fun x hx i j hij => by
    by_contra hne
    apply hx
    simp [density_eq_zero_of_collision ψ x hne hij]

/-- The unordered finite configuration underlying a labeled sample. -/
def configuration (x : Fin n → X) : Finset X := by
  classical
  exact Finset.univ.image x

/-- The projection law has exactly its rank many points almost surely. -/
theorem ae_card_configuration {μ : Measure X} {ψ : Fin n → X → ℂ}
    (hi : Integrable (squaredDet ψ) (Measure.pi fun _ : Fin n => μ)) :
    ∀ᵐ x ∂law μ ψ, (configuration x).card = n := by
  classical
  filter_upwards [ae_injective_law hi] with x hx
  simp [configuration, Finset.card_image_of_injective _ hx]

end ProbabilityTheory.ContinuousProjectionDPP
