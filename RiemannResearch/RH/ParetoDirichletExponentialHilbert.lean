import RiemannResearch.NumberTheory.DirichletExponential
import RiemannResearch.NumberTheory.DirichletExponentialBounds
import RiemannResearch.RH.MobiusDifferenceCLM

/-!
# From convolution-power energy bounds to the actual Hilbert exponential

Source: the Pareto Dirichlet-exponential argument, 13 November 2026.
This module isolates the general Banach-space assembly from the arithmetic
moment estimate.  Its hypotheses are quantitative bounds on the genuine
Dirichlet powers, and its conclusion concerns the actual coefficient series.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ConvolutionExponential

open RiemannResearch.NumberTheory.DirichletExponential

/-- Embed one actual Dirichlet power using its full Pareto energy. -/
def powerHilbert (f : ArithmeticFunction ℝ) (r : ℕ)
    (h : Summable (fun n => positiveWeight n * ((f ^ r) n) ^ 2)) :
    ThresholdHilbert := sequenceHilbert (fun n => (f ^ r) n) h

@[simp] theorem powerHilbert_sequence (f : ArithmeticFunction ℝ) (r : ℕ)
    (h : Summable (fun n => positiveWeight n * ((f ^ r) n) ^ 2)) :
    hilbertSequence (powerHilbert f r h) = fun n => (f ^ r) n := by
  apply hilbertSequence_sequenceHilbert
  simp

/-- A factorial energy bound gives absolute norm convergence of the genuine
Dirichlet Taylor series. -/
theorem powerHilbert_exp_norm_summable (f : ArithmeticFunction ℝ)
    (henergy : ∀ r : ℕ, Summable (fun n => positiveWeight n * ((f ^ r) n) ^ 2))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ r : ℕ,
      (∑' n : ℕ, positiveWeight n * ((f ^ r) n) ^ 2) ≤
        A ^ r * (r.factorial : ℝ)) :
    Summable (fun r : ℕ =>
      ‖(1 / (r.factorial : ℝ)) • powerHilbert f r (henergy r)‖) := by
  apply summable_norm_exp_terms_of_norm_sq_le_factorial _ hA
  intro r
  rw [hilbert_norm_weighted_sq, powerHilbert_sequence]
  exact hbound r

/-- A factorial energy bound gives convergence of the genuine Taylor series
in the complete Pareto Hilbert space. -/
theorem powerHilbert_exp_summable (f : ArithmeticFunction ℝ)
    (henergy : ∀ r : ℕ, Summable (fun n => positiveWeight n * ((f ^ r) n) ^ 2))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ r : ℕ,
      (∑' n : ℕ, positiveWeight n * ((f ^ r) n) ^ 2) ≤
        A ^ r * (r.factorial : ℝ)) :
    Summable (fun r : ℕ => (1 / (r.factorial : ℝ)) • powerHilbert f r (henergy r)) := by
  apply summable_exp_terms_of_norm_sq_le_factorial _ hA
  intro r
  rw [hilbert_norm_weighted_sq, powerHilbert_sequence]
  exact hbound r

/-- The Hilbert sum has exactly the coefficients of the infinite arithmetic
convolution exponential.  Coordinate evaluation is a continuous linear map. -/
theorem powerHilbert_exp_tsum_sequence (f : ArithmeticFunction ℝ)
    (henergy : ∀ r : ℕ, Summable (fun n => positiveWeight n * ((f ^ r) n) ^ 2))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ r : ℕ,
      (∑' n : ℕ, positiveWeight n * ((f ^ r) n) ^ 2) ≤
        A ^ r * (r.factorial : ℝ)) :
    hilbertSequence (∑' r : ℕ,
      (1 / (r.factorial : ℝ)) • powerHilbert f r (henergy r)) = convolutionExp f := by
  funext n
  have hs := powerHilbert_exp_summable f henergy hA hbound
  rw [← anchoredEvaluationCLM_apply n, (anchoredEvaluationCLM n).map_tsum hs]
  simp only [map_smul, anchoredEvaluationCLM_apply, powerHilbert_sequence,
    smul_eq_mul, one_div_mul_eq_div, convolutionExp]

/-- Quantitative power bounds prove membership of the actual arithmetic
exponential in the physical Pareto Hilbert space. -/
theorem convolutionExp_square_summable_of_power_energy (f : ArithmeticFunction ℝ)
    (henergy : ∀ r : ℕ, Summable (fun n => positiveWeight n * ((f ^ r) n) ^ 2))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ r : ℕ,
      (∑' n : ℕ, positiveWeight n * ((f ^ r) n) ^ 2) ≤
        A ^ r * (r.factorial : ℝ)) :
    Summable (fun n => positiveWeight n * (convolutionExp f n) ^ 2) := by
  have hs := hilbertSequence_square_summable (∑' r : ℕ,
    (1 / (r.factorial : ℝ)) • powerHilbert f r (henergy r))
  simpa only [powerHilbert_exp_tsum_sequence f henergy hA hbound] using hs


/-- The physical Pareto weight is dominated by the inverse-square weight. -/
theorem positiveWeight_mul_sq_le_inv_sq (a : ℝ) (n : ℕ) :
    positiveWeight n * a ^ 2 ≤ a ^ 2 / (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [positiveWeight]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hw : positiveWeight n ≤ 1 / (n : ℝ) ^ 2 := by
      unfold positiveWeight
      exact one_div_le_one_div_of_le (sq_pos_of_pos hnR) (by nlinarith)
    calc
      positiveWeight n * a ^ 2 ≤ (1 / (n : ℝ) ^ 2) * a ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg a)
      _ = a ^ 2 / (n : ℝ) ^ 2 := by ring

/-- Inverse-square summability is a sufficient actual Pareto energy estimate. -/
theorem weighted_square_summable_of_inv_sq (f : ℕ → ℝ)
    (hf : Summable (fun n => (f n) ^ 2 / (n : ℝ) ^ 2)) :
    Summable (fun n => positiveWeight n * (f n) ^ 2) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
    (fun n => positiveWeight_mul_sq_le_inv_sq (f n) n) hf

/-- The physical squared norm is bounded by the inverse-square moment. -/
theorem weighted_square_tsum_le_inv_sq (f : ℕ → ℝ)
    (hf : Summable (fun n => (f n) ^ 2 / (n : ℝ) ^ 2)) :
    (∑' n, positiveWeight n * (f n) ^ 2) ≤
      ∑' n, (f n) ^ 2 / (n : ℝ) ^ 2 :=
  (weighted_square_summable_of_inv_sq f hf).tsum_le_tsum
    (fun n => positiveWeight_mul_sq_le_inv_sq (f n) n) hf

/-- An inverse-square moment bound supplies the full Hilbert exponential. -/
theorem convolutionExp_square_summable_of_inv_sq_power_moments
    (f : ArithmeticFunction ℝ)
    (hs : ∀ r : ℕ, Summable (fun n => ((f ^ r) n) ^ 2 / (n : ℝ) ^ 2))
    {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ r : ℕ, (∑' n, ((f ^ r) n) ^ 2 / (n : ℝ) ^ 2) ≤
      A ^ r * (r.factorial : ℝ)) :
    Summable (fun n => positiveWeight n * (convolutionExp f n) ^ 2) := by
  apply convolutionExp_square_summable_of_power_energy f
    (fun r => weighted_square_summable_of_inv_sq _ (hs r)) hA
  intro r
  exact (weighted_square_tsum_le_inv_sq _ (hs r)).trans (hb r)

end RiemannResearch.RH.Pareto.ConvolutionExponential
