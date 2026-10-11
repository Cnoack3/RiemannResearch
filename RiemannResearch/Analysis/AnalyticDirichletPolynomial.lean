import RiemannResearch.Analysis.TruncatedMobiusConvolution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Entire finite Dirichlet polynomials and exact reciprocal convolution

Source: the user-provided ordinate harmonic-analysis development. The product
identity uses Mathlib's unconditional finite Möbius inversion, via the sibling
`TruncatedMobiusConvolution`. No sample law or RH hypothesis occurs.
-/

noncomputable section
open Complex
open scoped BigOperators

namespace RiemannResearch.Analysis.AnalyticDirichletPolynomial

/-- An entire finite Dirichlet polynomial, using real logarithms at positive
integer indices. This definition avoids a branch choice for complex powers. -/
def dirichletPolynomial (Y : ℕ) (c : ℕ → ℂ) (s : ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Y, c n *
    Complex.exp ((-s + (t : ℂ) * Complex.I) * (Real.log n : ℂ))

/-- For positive integers the exponential and complex-power conventions agree. -/
theorem dirichletWeight_eq_exp {n : ℕ} (hn : 0 < n) (s : ℂ) (t : ℝ) :
    TruncatedMobiusConvolution.dirichletWeight s t n =
      Complex.exp ((-s + (t : ℂ) * Complex.I) * (Real.log n : ℂ)) := by
  unfold TruncatedMobiusConvolution.dirichletWeight
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'),
    ← Complex.natCast_log]
  congr 1
  ring

theorem dirichletPolynomial_eq_weight_sum (Y : ℕ) (c : ℕ → ℂ) (s : ℂ) (t : ℝ) :
    dirichletPolynomial Y c s t = ∑ n ∈ Finset.Icc 1 Y,
      c n * TruncatedMobiusConvolution.dirichletWeight s t n := by
  unfold dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [dirichletWeight_eq_exp (Finset.mem_Icc.mp hn).1]

/-- Exact analytic product identity, retaining precisely the complete residual
support above the cutoff. This holds for every s and every real ordinate. -/
theorem zeta_mobius_product_eq_tail {Y : ℕ} (hY : 1 ≤ Y) (s : ℂ) (t : ℝ) :
    dirichletPolynomial Y (fun _ => 1) s t *
      dirichletPolynomial Y (fun n => (ArithmeticFunction.moebius n : ℂ)) s t - 1 =
    ∑ n ∈ Finset.Ioc Y (Y * Y),
      TruncatedMobiusConvolution.coefficient Y n *
        TruncatedMobiusConvolution.dirichletWeight s t n := by
  rw [dirichletPolynomial_eq_weight_sum, dirichletPolynomial_eq_weight_sum]
  simp only [one_mul]
  exact TruncatedMobiusConvolution.analytic_truncated_product_tail hY s t

theorem differentiable_dirichletPolynomial (Y : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    Differentiable ℂ (fun s => dirichletPolynomial Y c s t) := by
  unfold dirichletPolynomial
  apply Differentiable.fun_sum
  intro n hn
  exact (differentiable_const (c n)).mul
    (((differentiable_id.neg.add (differentiable_const ((t : ℂ) * Complex.I))).mul_const _).cexp)

theorem differentiable_product_error (Y : ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    Differentiable ℂ (fun s =>
      dirichletPolynomial Y a s t * dirichletPolynomial Y b s t - 1) :=
  ((differentiable_dirichletPolynomial Y a t).mul
    (differentiable_dirichletPolynomial Y b t)).sub (differentiable_const 1)


end RiemannResearch.Analysis.AnalyticDirichletPolynomial
