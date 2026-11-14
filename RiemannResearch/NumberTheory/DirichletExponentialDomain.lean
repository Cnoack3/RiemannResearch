import RiemannResearch.NumberTheory.DirichletExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Coefficientwise domain of the Dirichlet exponential

Source: the user's question about exp-star(V), 13 November 2026.
At a fixed arithmetic coordinate only finitely many input coefficients matter.
Thus scalar convergence does not require a global boundedness or Hilbert
hypothesis. The ordinary real exponential at coordinate 1 uses Mathlib's
scalar exponential-series identity; no convolution norm is installed on H.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.DirichletExponential

theorem convolutionPower_abs_le_of_local_bound (f : ArithmeticFunction ℝ)
    {C : ℝ} (hC : 0 ≤ C) (N : ℕ) (hf : ∀ m ≤ N, |f m| ≤ C) (r : ℕ) :
    ∀ m ≤ N, |(f ^ r) m| ≤ (C * ((N : ℝ) + 1)) ^ r := by
  have hA : 0 ≤ C * ((N : ℝ) + 1) := mul_nonneg hC (by positivity)
  induction r with
  | zero =>
      intro m hm
      simp only [pow_zero, ArithmeticFunction.one_apply]
      split_ifs <;> norm_num
  | succ r ih =>
      intro m hm
      rw [pow_succ, ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun d e => (f ^ r) d * f e)]
      calc
        |∑ d ∈ m.divisors, (f ^ r) d * f (m / d)| ≤
            ∑ d ∈ m.divisors, |(f ^ r) d * f (m / d)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d ∈ m.divisors, (C * ((N : ℝ) + 1)) ^ r * C := by
          apply Finset.sum_le_sum
          intro d hd
          rw [abs_mul]
          exact mul_le_mul (ih d ((Nat.divisor_le hd).trans hm))
            (hf (m / d) ((Nat.div_le_self m d).trans hm))
            (abs_nonneg _) (pow_nonneg hA r)
        _ = (m.divisors.card : ℝ) * ((C * ((N : ℝ) + 1)) ^ r * C) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((N : ℝ) + 1) * ((C * ((N : ℝ) + 1)) ^ r * C) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg hA r) hC)
          exact_mod_cast (Nat.card_divisors_le_self m).trans (by omega : m ≤ N + 1)
        _ = (C * ((N : ℝ) + 1)) ^ (r + 1) := by
          rw [pow_succ]
          ring

/-- Every real arithmetic input has an absolutely convergent exponential
series at each fixed coefficient, including unbounded inputs. -/
theorem convolutionExp_summable_at (f : ArithmeticFunction ℝ) (n : ℕ) :
    Summable (fun r : ℕ => (f ^ r) n / (r.factorial : ℝ)) := by
  let C : ℝ := ∑ m ∈ Finset.range (n + 1), |f m|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun m _ => abs_nonneg _)
  have hf : ∀ m ≤ n, |f m| ≤ C := by
    intro m hm
    exact Finset.single_le_sum (fun i _ => abs_nonneg (f i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  apply Summable.of_norm_bounded
    (Real.summable_pow_div_factorial (C * ((n : ℝ) + 1)))
  intro r
  rw [Real.norm_eq_abs, abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ (r.factorial : ℝ) from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right
    (convolutionPower_abs_le_of_local_bound f hC n hf r n le_rfl)
    (Nat.cast_nonneg _)

theorem convolutionExp_at_one (f : ArithmeticFunction ℝ) :
    convolutionExp f 1 = Real.exp (f 1) := by
  rw [convolutionExp_one_series, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

theorem convolutionExp_at_one_pos (f : ArithmeticFunction ℝ) :
    0 < convolutionExp f 1 := by
  rw [convolutionExp_at_one]
  exact Real.exp_pos _

theorem convolutionExp_ne_zero (f : ArithmeticFunction ℝ) :
    convolutionExp f ≠ (0 : ℕ → ℝ) := by
  intro h
  have hp := convolutionExp_at_one_pos f
  rw [h] at hp
  exact (lt_irrefl 0) hp

/-- The quadratic term is a genuine lower bound without boundedness. -/
theorem convolutionExp_quadratic_lower_of_nonneg
    (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n) (n : ℕ) :
    (f * f) n / 2 ≤ convolutionExp f n := by
  have h := (convolutionExp_summable_at f n).le_tsum 2 (fun r _ =>
    div_nonneg (convolutionPower_nonneg f hf r n) (Nat.cast_nonneg _))
  simpa only [convolutionExp, pow_two, Nat.factorial_two, Nat.cast_ofNat] using h

end RiemannResearch.NumberTheory.DirichletExponential
