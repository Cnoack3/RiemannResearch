import RiemannResearch.Analysis.FinitePolynomialSampling
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite sample resonance destroys a uniform upper bound

Source: user-provided V_vector_space_RH.pdf, Section 4. The explicit polynomial
uses only positive powers, so evaluation on the phase 2^(I*t) is a one-prime
Dirichlet polynomial. A single unit-modulus sample suffices; multiplicities and
all other sample terms are retained in the lower estimate.
-/

noncomputable section
open scoped BigOperators
namespace Polynomial

def resonancePolynomial (z : ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.Icc 1 d, monomial k (star z ^ k)

theorem resonancePolynomial_coeff (z : ℂ) (d k : ℕ) :
    (resonancePolynomial z d).coeff k =
      if k ∈ Finset.Icc 1 d then star z ^ k else 0 := by
  classical
  simp [resonancePolynomial, coeff_monomial]

theorem resonancePolynomial_support (z : ℂ) (hz : ‖z‖ = 1) (d : ℕ) :
    (resonancePolynomial z d).support = Finset.Icc 1 d := by
  classical
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  ext k
  rw [mem_support_iff, resonancePolynomial_coeff]
  by_cases hk : k ∈ Finset.Icc 1 d
  · simp [hk, hz0]
  · simp [hk]

theorem resonancePolynomial_eval_zero (z : ℂ) (d : ℕ) :
    (resonancePolynomial z d).eval 0 = 0 := by
  simp only [resonancePolynomial, eval_finsetSum, eval_monomial]
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : k ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  simp [hk0]

theorem resonancePolynomial_eval_self (z : ℂ) (hz : ‖z‖ = 1) (d : ℕ) :
    (resonancePolynomial z d).eval z = (d : ℂ) := by
  have hunit : star z * z = 1 := by
    have h := Complex.mul_conj z
    rw [Complex.normSq_eq_norm_sq, hz] at h
    simpa [mul_comm] using h
  simp only [resonancePolynomial, eval_finsetSum, eval_monomial]
  simp_rw [← mul_pow, hunit, one_pow]
  simp

theorem resonancePolynomial_coefficient_energy (z : ℂ) (hz : ‖z‖ = 1) (d : ℕ) :
    coefficientSquareEnergy (resonancePolynomial z d) = (d : ℝ) := by
  unfold coefficientSquareEnergy
  rw [resonancePolynomial_support z hz]
  calc
    _ = ∑ k ∈ Finset.Icc 1 d, ‖star z ^ k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [resonancePolynomial_coeff, if_pos hk]
    _ = (d : ℝ) := by simp [norm_pow, hz]

theorem resonancePolynomial_sample_energy_ge {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (i : ι) (hi : i ∈ s) (hz : ‖z i‖ = 1) (d : ℕ) :
    (d : ℝ)^2 ≤ sampledSquareEnergy s z (resonancePolynomial (z i) d) := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ s) =>
    sq_nonneg ‖(resonancePolynomial (z i) d).eval (z j)‖) hi
  rw [resonancePolynomial_eval_self (z i) hz d] at h
  simpa [sampledSquareEnergy] using h

/-- The upper sampling operator is unbounded on unrestricted coefficient support
already at one fixed, nonempty sampling height. -/
theorem no_uniform_upper_sampling_bound {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (i : ι) (hi : i ∈ s) (hz : ‖z i‖ = 1) :
    ¬ ∃ B : ℝ, ∀ P : Polynomial ℂ, P.eval 0 = 0 →
      sampledSquareEnergy s z P ≤ B * coefficientSquareEnergy P := by
  rintro ⟨B, hB⟩
  obtain ⟨d, hd⟩ := exists_nat_gt (max B 0)
  have hdB : B < (d:ℝ) := lt_of_le_of_lt (le_max_left _ _) hd
  have hd0 : 0 < (d:ℝ) := lt_of_le_of_lt (le_max_right _ _) hd
  have hupper := hB (resonancePolynomial (z i) d)
    (resonancePolynomial_eval_zero (z i) d)
  rw [resonancePolynomial_coefficient_energy (z i) hz d] at hupper
  have hlower := resonancePolynomial_sample_energy_ge s z i hi hz d
  nlinarith

/-- Centering by the exact sample count does not repair the fixed-height upper
obstruction. No zero-count asymptotic is needed for this direction. -/
theorem no_uniform_centered_upper_bound {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (i : ι) (hi : i ∈ s) (hz : ‖z i‖ = 1)
    (T : ℝ) (hT : 0 < T) :
    ¬ ∃ C : ℝ, ∀ P : Polynomial ℂ, P.eval 0 = 0 →
      (sampledSquareEnergy s z P - (s.card:ℝ)*coefficientSquareEnergy P)/T ≤
        C*coefficientSquareEnergy P := by
  rintro ⟨C, hC⟩
  apply no_uniform_upper_sampling_bound s z i hi hz
  refine ⟨C*T+(s.card:ℝ), ?_⟩
  intro P hP
  have h := (div_le_iff₀ hT).mp (hC P hP)
  nlinarith

/-- The concrete powers-of-two specialization from the manuscript. -/
theorem no_uniform_one_prime_centered_upper_bound {ι : Type*}
    (s : Finset ι) (times : ι → ℝ) (i : ι) (hi : i ∈ s)
    (T : ℝ) (hT : 0 < T) :
    ¬ ∃ C : ℝ, ∀ P : Polynomial ℂ, P.eval 0 = 0 →
      (sampledSquareEnergy s
          (fun j => Complex.exp ((times j * Real.log 2 : ℝ) * Complex.I)) P -
        (s.card:ℝ)*coefficientSquareEnergy P)/T ≤
        C*coefficientSquareEnergy P :=
  no_uniform_centered_upper_bound s _ i hi
    (Complex.norm_exp_ofReal_mul_I _) T hT

end Polynomial
