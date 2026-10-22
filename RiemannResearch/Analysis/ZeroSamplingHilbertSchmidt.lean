import RiemannResearch.Analysis.ZeroSamplingQuadratic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hilbert--Schmidt transfer for finite zero-sampling forms

Source: user-provided zero-ordinate harmonic analysis note (2026-10-11).
The Cauchy--Schwarz estimates here are unconditional finite linear algebra.
The logarithmic and fourth-moment specializations explicitly assume their
analytic entrywise and moment budgets; this module supplies no Landau or
zero-density theorem and assumes no RH.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ZeroSamplingQuadratic

variable {ι : Type*}

/-- Exact squared Hilbert--Schmidt energy of a finite matrix. -/
def matrixSquareEnergy (s : Finset ι) (R : ι → ι → ℂ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, ‖R i j‖ ^ 2

theorem matrixSquareEnergy_nonneg (s : Finset ι) (R : ι → ι → ℂ) :
    0 ≤ matrixSquareEnergy s R := by
  apply Finset.sum_nonneg
  intro i hi
  exact Finset.sum_nonneg (fun j hj => sq_nonneg _)

/-- The full coefficient-weighted finite Cauchy--Schwarz estimate. -/
theorem form_hilbertSchmidt_bound (s : Finset ι)
    (R : ι → ι → ℂ) (a : ι → ℂ) :
    ‖form s R a‖ ≤ Real.sqrt (matrixSquareEnergy s R) * coefficientEnergy s a := by
  classical
  let P : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * ‖R i j‖
  have hnorm : ‖form s R a‖ ≤ P := by
    unfold form
    apply le_trans (norm_sum_le _ _)
    apply Finset.sum_le_sum
    intro i hi
    apply le_trans (norm_sum_le _ _)
    apply Finset.sum_le_sum
    intro j hj
    simp only [norm_mul, norm_star]
    exact le_rfl
  have hP : 0 ≤ P := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    positivity
  have hcoeff : (∑ i ∈ s, ∑ j ∈ s, (‖a i‖ * ‖a j‖) ^ 2) =
      coefficientEnergy s a ^ 2 := by
    simp only [coefficientEnergy, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s ×ˢ s)
    (fun ij => ‖a ij.1‖ * ‖a ij.2‖) (fun ij => ‖R ij.1 ij.2‖)
  rw [@Finset.sum_product ι ℝ ι (inferInstance : CommSemiring ℝ).toAddCommMonoid s s (fun ij => ‖a ij.1‖ * ‖a ij.2‖ * ‖R ij.1 ij.2‖),
    @Finset.sum_product ι ℝ ι (inferInstance : CommSemiring ℝ).toAddCommMonoid s s (fun ij => (‖a ij.1‖ * ‖a ij.2‖) ^ 2),
    @Finset.sum_product ι ℝ ι (inferInstance : CommSemiring ℝ).toAddCommMonoid s s (fun ij => ‖R ij.1 ij.2‖ ^ 2), hcoeff] at hcs
  change P ^ 2 ≤ coefficientEnergy s a ^ 2 * matrixSquareEnergy s R at hcs
  have hE := coefficientEnergy_nonneg s a
  have hR := matrixSquareEnergy_nonneg s R
  have hsqrt := Real.sqrt_nonneg (matrixSquareEnergy s R)
  have hproduct :
      (Real.sqrt (matrixSquareEnergy s R) * coefficientEnergy s a) ^ 2 =
        coefficientEnergy s a ^ 2 * matrixSquareEnergy s R := by
    rw [mul_pow, Real.sq_sqrt hR]
    ring
  have hPbound : P ≤ Real.sqrt (matrixSquareEnergy s R) * coefficientEnergy s a := by
    nlinarith [mul_nonneg hsqrt hE]
  exact hnorm.trans hPbound

/-- Hilbert--Schmidt comparison, without a support-cardinality estimate. -/
theorem form_comparison_hilbertSchmidt (s : Finset ι)
    (G H : ι → ι → ℂ) (a : ι → ℂ) :
    ‖form s G a - form s H a‖ ≤
      Real.sqrt (matrixSquareEnergy s (fun i j => G i j - H i j)) *
        coefficientEnergy s a := by
  rw [← form_sub]
  exact form_hilbertSchmidt_bound s _ a

/-- A supplied matrix-square budget becomes a coefficient-uniform bound. -/
theorem form_hilbertSchmidt_bound_of_budget (s : Finset ι)
    (R : ι → ι → ℂ) (a : ι → ℂ) (M : ℝ)
    (hbudget : matrixSquareEnergy s R ≤ M) :
    ‖form s R a‖ ≤ Real.sqrt M * coefficientEnergy s a := by
  exact (form_hilbertSchmidt_bound s R a).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hbudget)
      (coefficientEnergy_nonneg s a))

/-- Explicit logarithmic even-moment transfer. Both the analytic approximation
and its moment budget are visible hypotheses, not newly proved zeta estimates. -/
theorem logarithmic_matrix_budget_transfer (s : Finset ι)
    (S H A : ι → ι → ℂ) (a : ι → ℂ) (d L X η : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (happrox : ∀ i ∈ s, ∀ j ∈ s,
      ‖S i j - H i j - (d / L : ℂ) * A i j‖ ≤ η)
    (hmoment : matrixSquareEnergy s A ≤ 24 * X * (X + 1)) :
    ‖form s S a - form s H a‖ ≤
      (d * Real.sqrt (24 * X * (X + 1)) / L + η * (s.card : ℝ)) *
        coefficientEnergy s a := by
  let R : ι → ι → ℂ := fun i j => S i j - H i j - (d / L : ℂ) * A i j
  have hdecomp : form s S a - form s H a =
      (d / L : ℂ) * form s A a + form s R a := by
    dsimp [R]
    simp only [form_sub, form_mul]
    ring
  have hA := form_hilbertSchmidt_bound_of_budget s A a _ hmoment
  have hR := form_bound s R a η hη happrox
  have hscale :
      ‖(d / L : ℂ) * form s A a‖ ≤
        (d / L) * (Real.sqrt (24 * X * (X + 1)) * coefficientEnergy s a) := by
    rw [norm_mul, ← Complex.ofReal_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg hd hL.le)]
    exact mul_le_mul_of_nonneg_left hA (div_nonneg hd hL.le)
  calc
    ‖form s S a - form s H a‖ =
        ‖(d / L : ℂ) * form s A a + form s R a‖ := congrArg norm hdecomp
    _ ≤ ‖(d / L : ℂ) * form s A a‖ + ‖form s R a‖ := norm_add_le _ _
    _ ≤ (d / L) * (Real.sqrt (24 * X * (X + 1)) * coefficientEnergy s a) +
        (s.card : ℝ) * η * coefficientEnergy s a := add_le_add hscale hR
    _ = _ := by
      simp only [div_eq_mul_inv]
      ring

/-- Exact fourth-moment budget for the squared Fourier-coefficient kernel. -/
theorem matrixSquareEnergy_norm_square (s : Finset ι) (A : ι → ι → ℂ) :
    matrixSquareEnergy s (fun i j => (‖A i j‖ ^ 2 : ℂ)) =
      ∑ i ∈ s, ∑ j ∈ s, ‖A i j‖ ^ 4 := by
  unfold matrixSquareEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [← Complex.ofReal_pow, Complex.norm_of_nonneg (sq_nonneg _)]
  ring

/-- A fourth-moment provider controls the entire squared-coefficient form,
uniformly in its potentially data-dependent coefficient vector. -/
theorem squared_kernel_hilbertSchmidt_bound_of_fourth_moment
    (s : Finset ι) (A : ι → ι → ℂ) (a : ι → ℂ) (M₄ : ℝ)
    (hmoment : (∑ i ∈ s, ∑ j ∈ s, ‖A i j‖ ^ 4) ≤ M₄) :
    ‖form s (fun i j => (‖A i j‖ ^ 2 : ℂ)) a‖ ≤
      Real.sqrt M₄ * coefficientEnergy s a := by
  apply form_hilbertSchmidt_bound_of_budget
  simpa only [matrixSquareEnergy_norm_square] using hmoment

/-- Real nonnegative entry envelopes need no aligned complex approximation.
This is the weighted Cauchy--Schwarz estimate used by the actual zero-sum bound. -/
theorem weighted_envelope_hilbertSchmidt_bound (s : Finset ι)
    (a : ι → ℂ) (E : ι → ι → ℝ) (M : ℝ)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (hbudget : (∑ i ∈ s, ∑ j ∈ s, E i j ^ 2) ≤ M) :
    (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j) ≤
      Real.sqrt M * coefficientEnergy s a := by
  classical
  let P : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j
  let Q : ℝ := ∑ i ∈ s, ∑ j ∈ s, E i j ^ 2
  have hP : 0 ≤ P := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (by positivity) (hE i hi j hj)
  have hQ : 0 ≤ Q := by
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hcoeff : (∑ i ∈ s, ∑ j ∈ s, (‖a i‖ * ‖a j‖) ^ 2) =
      coefficientEnergy s a ^ 2 := by
    simp only [coefficientEnergy, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s ×ˢ s)
    (fun ij => ‖a ij.1‖ * ‖a ij.2‖) (fun ij => E ij.1 ij.2)
  rw [@Finset.sum_product ι ℝ ι (inferInstance : CommSemiring ℝ).toAddCommMonoid s s (fun ij => ‖a ij.1‖ * ‖a ij.2‖ * E ij.1 ij.2),
    @Finset.sum_product ι ℝ ι (inferInstance : CommSemiring ℝ).toAddCommMonoid s s (fun ij => (‖a ij.1‖ * ‖a ij.2‖) ^ 2),
    @Finset.sum_product ι ℝ ι (inferInstance : CommSemiring ℝ).toAddCommMonoid s s (fun ij => E ij.1 ij.2 ^ 2), hcoeff] at hcs
  change P ^ 2 ≤ coefficientEnergy s a ^ 2 * Q at hcs
  have hcoef := coefficientEnergy_nonneg s a
  have hsqrt := Real.sqrt_nonneg Q
  have hproduct : (Real.sqrt Q * coefficientEnergy s a) ^ 2 =
      coefficientEnergy s a ^ 2 * Q := by
    rw [mul_pow, Real.sq_sqrt hQ]
    ring
  have hPbound : P ≤ Real.sqrt Q * coefficientEnergy s a := by
    nlinarith [mul_nonneg hsqrt hcoef]
  exact hPbound.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt hbudget) hcoef)

/-- A norm envelope is sufficient: no common complex direction for the
entry errors is assumed. The dense error is retained separately as `η * card`. -/
theorem form_comparison_envelope_hilbertSchmidt (s : Finset ι)
    (S H : ι → ι → ℂ) (a : ι → ℂ) (c η : ℝ) (E : ι → ι → ℝ) (M : ℝ)
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (hentry : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - H i j‖ ≤ c * E i j + η)
    (hbudget : (∑ i ∈ s, ∑ j ∈ s, E i j ^ 2) ≤ M) :
    ‖form s S a - form s H a‖ ≤
      (c * Real.sqrt M + η * (s.card : ℝ)) * coefficientEnergy s a := by
  have hnorm : ‖form s S a - form s H a‖ ≤
      ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (c * E i j + η) := by
    rw [← form_sub]
    unfold form
    apply le_trans (norm_sum_le _ _)
    apply Finset.sum_le_sum
    intro i hi
    apply le_trans (norm_sum_le _ _)
    apply Finset.sum_le_sum
    intro j hj
    simp only [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (hentry i hi j hj) (by positivity)
  have hweighted := weighted_envelope_hilbertSchmidt_bound s a E M hE hbudget
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hdense : (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖) ≤
      (s.card : ℝ) * coefficientEnergy s a := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖) = (∑ i ∈ s, ‖a i‖) ^ 2 := by
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ (s.card : ℝ) * coefficientEnergy s a := hcs
  calc
    ‖form s S a - form s H a‖ ≤
        ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (c * E i j + η) := hnorm
    _ = c * (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j) +
        η * (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ c * (Real.sqrt M * coefficientEnergy s a) +
        η * ((s.card : ℝ) * coefficientEnergy s a) :=
      add_le_add (mul_le_mul_of_nonneg_left hweighted hc)
        (mul_le_mul_of_nonneg_left hdense hη)
    _ = _ := by ring

/-- The explicit logarithmic bound from a real norm envelope, the hypothesis
available from the paper's zero-sum estimate. -/
theorem logarithmic_norm_envelope_transfer (s : Finset ι)
    (S H : ι → ι → ℂ) (a : ι → ℂ) (d L X η : ℝ) (E : ι → ι → ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (hentry : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - H i j‖ ≤ (d / L) * E i j + η)
    (hbudget : (∑ i ∈ s, ∑ j ∈ s, E i j ^ 2) ≤ 24 * X * (X + 1)) :
    ‖form s S a - form s H a‖ ≤
      (d * Real.sqrt (24 * X * (X + 1)) / L + η * (s.card : ℝ)) *
        coefficientEnergy s a := by
  calc
    ‖form s S a - form s H a‖ ≤
        ((d / L) * Real.sqrt (24 * X * (X + 1)) + η * (s.card : ℝ)) *
          coefficientEnergy s a :=
      form_comparison_envelope_hilbertSchmidt s S H a (d / L) η E _
        (div_nonneg hd hL.le) hη hE hentry hbudget
    _ = _ := by
      simp only [div_eq_mul_inv]
      ring

end RiemannResearch.Analysis.ZeroSamplingQuadratic
