import RiemannResearch.Analysis.LogEulerFeature
import RiemannResearch.Analysis.CoherentFock
import RiemannResearch.Analysis.ZetaDirichletKernel
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
/-!
# The actual zeta kernel from prime-power coherent vectors
Source: V_vector_space_RH.pdf, Section 5.1.
The logarithmic feature has coordinates p^(-s(k+1))/sqrt(k+1).
Mathlib's proved zeta Euler product identifies the coherent Gram kernel.
The equality of finite-combination norms identifies the algebraic spans
isometrically. Explicit occupation grouping by integers is not used here.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ZetaFockKernel
open SampledGauge
def primeFeature (s : ℂ) (p : Nat.Primes) : ℂ :=
  Complex.exp (-s * (Real.log (p.1 : ℝ) : ℂ))

theorem primeFeature_cpow (s : ℂ) (p : Nat.Primes) :
    primeFeature s p = (p.1 : ℂ) ^ (-s) := by
  have hp : (0 : ℝ) < p.1 := Nat.cast_pos.mpr p.property.pos
  have hpC : (p.1 : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hp.le]
  unfold primeFeature
  congr 1
  ring

theorem primeFeature_norm_sq (s : ℂ) (p : Nat.Primes) :
    ‖primeFeature s p‖ ^ 2 = (p.1 : ℝ) ^ (-2 * s.re) := by
  rw [primeFeature, Complex.norm_exp, ← Real.exp_nat_mul,
    Real.rpow_def_of_pos (Nat.cast_pos.mpr p.property.pos)]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  congr 1
  ring

theorem primeFeature_summable_sq (s : ℂ) (hs : 1 / 2 < s.re) :
    Summable (fun p => ‖primeFeature s p‖ ^ 2) := by
  simp only [primeFeature_norm_sq]
  exact Nat.Primes.summable_rpow.mpr (by linarith)

theorem primeFeature_norm_lt_one (s : ℂ) (hs : 1 / 2 < s.re) (p : Nat.Primes) :
    ‖primeFeature s p‖ < 1 := by
  rw [primeFeature, Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have hp : 0 < Real.log (p.1 : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  exact mul_neg_of_neg_of_pos (by linarith) hp

theorem primeFeature_pair (s w : ℂ) (p : Nat.Primes) :
    star (primeFeature s p) * primeFeature w p = primeFeature (star s + w) p := by
  change (starRingEnd ℂ) (Complex.exp _) * Complex.exp _ = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp only [map_mul, map_neg, Complex.conj_ofReal, primeFeature, Complex.star_def]
  congr 1
  ring

def logVector (s : ℂ) (hs : 1 / 2 < s.re) : Space (Nat.Primes × ℕ) :=
  LogEulerFeature.vector (primeFeature s) (primeFeature_summable_sq s hs)
    (primeFeature_norm_lt_one s hs)

theorem logVector_inner (s w : ℂ) (hs : 1 / 2 < s.re) (hw : 1 / 2 < w.re) :
    inner ℂ (logVector s hs) (logVector w hw) =
      ∑' p : Nat.Primes, -Complex.log (1 - (p.1 : ℂ) ^ (-(star s + w))) := by
  rw [logVector, logVector, LogEulerFeature.vector_inner]
  simp_rw [primeFeature_pair, primeFeature_cpow]

def coherent (s : ℂ) (hs : 1 / 2 < s.re) :=
  CoherentFock.vector (logVector s hs)

theorem coherent_inner (s w : ℂ) (hs : 1 / 2 < s.re) (hw : 1 / 2 < w.re) :
    inner ℂ (coherent s hs) (coherent w hw) = riemannZeta (star s + w) := by
  rw [coherent, coherent, CoherentFock.vector_inner, logVector_inner]
  apply riemannZeta_eulerProduct_exp_log
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  linarith

theorem coherent_gram_eq_integer_gram (s w : ℂ)
    (hs : 1 / 2 < s.re) (hw : 1 / 2 < w.re) :
    inner ℂ (coherent s hs) (coherent w hw) =
      inner ℂ (ZetaDirichletKernel.vector s hs) (ZetaDirichletKernel.vector w hw) := by
  rw [coherent_inner, ZetaDirichletKernel.vector_inner]

theorem coherent_norm_sq (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖coherent s hs‖ ^ 2 = (riemannZeta (star s + s)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), coherent_inner]
  rfl

theorem finite_combination_norm_eq {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    ‖∑ i, c i • coherent (s i) (hs i)‖ =
      ‖∑ i, c i • ZetaDirichletKernel.vector (s i) (hs i)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  congr 1
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    coherent_gram_eq_integer_gram]

end RiemannResearch.Analysis.ZetaFockKernel
