import RiemannResearch.NumberTheory.DirichletExponentialPrimePowers
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Scalar exponential coordinates and universal coefficient bounds

Source: the user-provided Pareto exponential argument. The first coefficient
is the usual scalar exponential, and bounded arithmetic functions are dominated
in every convolution power by a scaled constant-one arithmetic function.
-/

noncomputable section

namespace RiemannResearch.NumberTheory.DirichletExponential

open scoped BigOperators

/-- At the multiplicative identity, the convolution exponential is the ordinary
real exponential. -/
theorem convolutionExp_one (f : ArithmeticFunction ℝ) :
    convolutionExp f 1 = Real.exp (f 1) := by
  rw [convolutionExp_one_series, Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp (f 1)).tsum_eq

/-- In particular the normalized-residue exponential has first coefficient
`exp (1/p)`, because `g_p(1)=1/p`. -/
theorem residueAF_exp_one {p : ℕ} (hp : 1 < p) :
    convolutionExp (residueAF p) 1 = Real.exp (1 / (p : ℝ)) := by
  rw [convolutionExp_one, residueAF_one hp]

/-- The sharp universal majorant for the coefficient of a convolution power
of a uniformly bounded arithmetic function. -/
theorem convolutionPower_abs_le_zetaReal (f : ArithmeticFunction ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) (r n : ℕ) :
    |(f ^ r) n| ≤ C ^ r * (zetaReal ^ r) n := by
  have hfζ : ∀ m, |f m| ≤ C * zetaReal m := by
    intro m
    by_cases hm : m = 0
    · subst m
      simp
    · simpa only [zetaReal_apply, if_neg hm, mul_one] using hf m
  induction r generalizing n with
  | zero =>
      simp only [pow_zero, one_mul, ArithmeticFunction.one_apply]
      split_ifs <;> norm_num
  | succ r ih =>
      rw [pow_succ, ArithmeticFunction.mul_apply]
      calc
        |∑ d ∈ n.divisorsAntidiagonal, (f ^ r) d.1 * f d.2|
            ≤ ∑ d ∈ n.divisorsAntidiagonal, |(f ^ r) d.1 * f d.2| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ n.divisorsAntidiagonal,
            (C ^ r * (zetaReal ^ r) d.1) * (C * zetaReal d.2) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [abs_mul]
          exact mul_le_mul (ih d.1) (hfζ d.2) (abs_nonneg _)
            (mul_nonneg (pow_nonneg hC r)
              (convolutionPower_nonneg zetaReal zetaReal_nonneg r d.1))
        _ = C ^ (r + 1) * (zetaReal ^ (r + 1)) n := by
          rw [pow_succ, pow_succ, ArithmeticFunction.mul_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring

/-- The same universal majorant controls the absolute value of every scalar
convolution-exponential coefficient. -/
theorem convolutionExp_abs_le_scaled_zetaReal (f : ArithmeticFunction ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) (n : ℕ) :
    |convolutionExp f n| ≤ convolutionExp (C • zetaReal) n := by
  have hg : ∀ m, |(C • zetaReal) m| ≤ C := by
    intro m
    change |C * zetaReal m| ≤ C
    rw [abs_mul, abs_of_nonneg hC]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (zetaReal_abs_le_one m) hC
  have hsf := convolutionExp_summable f hC hf n
  have hsg := convolutionExp_summable (C • zetaReal) hC hg n
  have hterm : ∀ r : ℕ,
      ‖(f ^ r) n / (r.factorial : ℝ)‖ ≤
        ((C • zetaReal) ^ r) n / (r.factorial : ℝ) := by
    intro r
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ (r.factorial : ℝ) from Nat.cast_nonneg _)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [smul_pow]
    change |(f ^ r) n| ≤ C ^ r * (zetaReal ^ r) n
    exact convolutionPower_abs_le_zetaReal f hC hf r n
  calc
    |convolutionExp f n| = ‖∑' r : ℕ, (f ^ r) n / (r.factorial : ℝ)‖ := by
      rw [convolutionExp, Real.norm_eq_abs]
    _ ≤ ∑' r : ℕ, ‖(f ^ r) n / (r.factorial : ℝ)‖ :=
      norm_tsum_le_tsum_norm hsf.norm
    _ ≤ ∑' r : ℕ, ((C • zetaReal) ^ r) n / (r.factorial : ℝ) :=
      Summable.tsum_le_tsum hterm hsf.norm hsg
    _ = convolutionExp (C • zetaReal) n := rfl

end RiemannResearch.NumberTheory.DirichletExponential
