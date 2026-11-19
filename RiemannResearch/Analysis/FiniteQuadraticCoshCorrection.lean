/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroBadPhaseTail
import RiemannResearch.Analysis.FiniteHyperbolicHarmonicCap
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quadratic Euclidean norm bound for a single horizontal shift

The Frobenius square of the correction is an exact combination of four
finite exponential sums. The positive even Taylor series scales
quadratically from any larger reference displacement. At reference
displacement 3/8 the integer-frequency power sums give a bound linear
in the dimension, without a logarithm of the dimension. Every phase
has modulus one, so the ordinate has no effect on this estimate.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate ZeroOrdinate HorizontalEuclideanMoments HorizontalPhaseBootstrap
open FiniteHyperbolicHarmonicCap

/-- Scaling each positive even Taylor coefficient retains the square of
the dilation. This estimate is uniform over the entire real argument. -/
theorem cosh_sub_one_mul_le_quadratic {θ x : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) :
    Real.cosh (θ * x) - 1 ≤ θ ^ 2 * (Real.cosh x - 1) := by
  rw [← cosh_tail_tsum, ← cosh_tail_tsum, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (cosh_tail_summable _) ((cosh_tail_summable _).mul_left _)
  intro k
  have hpow : θ ^ (2 * (k+1)) ≤ θ ^ 2 := by
    rw [show 2 * (k+1) = 2 + 2*k by omega, pow_add]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ h₀ h₁)
  have hxp : 0 ≤ x ^ (2*(k+1)) := by rw [pow_mul]; positivity
  rw [mul_pow]
  calc
    _ ≤ (θ ^ 2 * x ^ (2*(k+1))) / (Nat.factorial (2*(k+1)) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hxp) (by positivity)
    _ = _ := by ring

def coshFrobeniusSquare {d : ℕ} (x : Fin d → ℝ) (a : ℝ) : ℝ :=
  ∑ n, ∑ m, (Real.cosh (a*(x n-x m)) - 1)^2

/-- Exact cancellation of the constant and linear products in the
Frobenius square. All sums are finite at every dimension. -/
theorem coshFrobeniusSquare_eq {d : ℕ} (x : Fin d → ℝ) (a : ℝ) :
    2 * coshFrobeniusSquare x a =
      finiteExponentialSum x (2*a) * finiteExponentialSum x (-(2*a)) -
      4 * (finiteExponentialSum x a * finiteExponentialSum x (-a)) + 3 * (d : ℝ)^2 := by
  have h (n m : Fin d) : 2 * (Real.cosh (a*(x n-x m))-1)^2 =
      Real.cosh ((2*a)*(x n-x m)) - 4 * Real.cosh (a*(x n-x m)) + 3 := by
    rw [mul_assoc, Real.cosh_two_mul]
    nlinarith only [Real.cosh_sq (a*(x n-x m))]
  rw [finiteExponentialProduct_eq_cosh, finiteExponentialProduct_eq_cosh]
  unfold coshFrobeniusSquare
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem exponentialProduct_ge_card_sq {d : ℕ} (x : Fin d → ℝ) (a : ℝ) :
    (d : ℝ)^2 ≤ finiteExponentialSum x a * finiteExponentialSum x (-a) := by
  rw [finiteExponentialProduct_eq_cosh]
  calc
    _ = ∑ _n : Fin d, ∑ _m : Fin d, (1 : ℝ) := by simp [sq]
    _ ≤ _ := Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => Real.one_le_cosh _

private theorem integerFrequencySum_eq_rpow (d : ℕ) (p : ℝ) :
    finiteExponentialSum (integerLogFrequency d) p =
      ∑ i ∈ Finset.range d, ((i+1 : ℕ) : ℝ)^p := by
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ))]
  unfold integerLogFrequency
  rw [mul_comm]

private theorem negative_powerSum_le (d : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp' : p < 1) :
    (∑ i ∈ Finset.range d, ((i+1 : ℕ) : ℝ)^(-p)) ≤ (d : ℝ)^(1-p)/(1-p) := by
  cases d with
  | zero =>
    simp [Real.zero_rpow (sub_ne_zero.mpr hp'.ne')]
  | succ k =>
    let f := fun x : ℝ => x ^ (-p)
    have ha : AntitoneOn f (Icc (1 : ℝ) (1 + (k : ℝ))) := by
      intro x hx y _ hxy
      exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx.1) hxy (neg_nonpos.mpr hp)
    have h := AntitoneOn.sum_le_integral ha
    rw [integral_rpow (Or.inl (show -1 < -p by linarith only [hp'])),
      Real.one_rpow, show -p + 1 = 1-p by ring] at h
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.zero_add, Real.one_rpow,
      Nat.cast_succ, add_comm (1 : ℝ) (k : ℝ), f] at h ⊢
    have hs : (∑ i ∈ Finset.range k, ((i : ℝ)+1+1)^(-p)) ≤
        (((k : ℝ)+1)^(1-p)-1)/(1-p) := by
      simpa only [add_comm (1 : ℝ) ((_:ℝ)+1)] using h
    simp only [Nat.cast_zero, zero_add, Real.one_rpow]
    apply (show (∑ i ∈ Finset.range k, ((i : ℝ)+1+1)^(-p)) + 1 ≤
      ((((k : ℝ)+1)^(1-p)-1)/(1-p)) + 1 by linarith only [hs]).trans
    apply (le_div_iff₀ (sub_pos.mpr hp')).mpr
    rw [add_mul, div_mul_cancel₀ _ (sub_pos.mpr hp').ne', one_mul]
    linarith only [hp]

private theorem positive_powerSum_le (d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (∑ i ∈ Finset.range d, ((i+1 : ℕ) : ℝ)^p) ≤ (d : ℝ) * (d : ℝ)^p := by
  calc
    _ ≤ ∑ _i ∈ Finset.range d, (d : ℝ)^p := by
      apply Finset.sum_le_sum
      intro i hi
      have hnat : i+1 ≤ d := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnat) hp
    _ = _ := by simp

/-- The real parameter range p < 1 is exactly the integrable range for
the negative integer power sum. -/
theorem finiteIntegerExponentialProduct_le {d : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p < 1) :
    finiteExponentialSum (integerLogFrequency d) p *
      finiteExponentialSum (integerLogFrequency d) (-p) ≤ (d : ℝ)^2 / (1-p) := by
  by_cases hd : d = 0
  · subst d; simp [finiteExponentialSum]
  have hdp : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  rw [integerFrequencySum_eq_rpow, integerFrequencySum_eq_rpow]
  calc
    _ ≤ ((d : ℝ) * (d : ℝ)^p) * ((d : ℝ)^(1-p)/(1-p)) :=
      mul_le_mul (positive_powerSum_le d hp) (negative_powerSum_le d hp hp')
        (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by
      rw [mul_div_assoc', mul_assoc, ← Real.rpow_add hdp, show p + (1-p) = 1 by ring,
        Real.rpow_one, sq]

/-- The Euclidean operator norm is bounded by the Frobenius norm of the
matrix. The proof uses finite Cauchy–Schwarz in the given coordinates. -/
theorem euclideanCLM_norm_le_of_sq_sum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    {K : ℝ} (hK : 0 ≤ K) (hs : (∑ i, ∑ j, ‖A i j‖^2) ≤ K^2) : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  have hf (i : Fin d) : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A v i‖^2 ≤ (∑ j, ‖A i j‖^2) * ‖v‖^2 := by
    have hi : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A v i = ∑ j, A i j * v j := by
      exact congrFun (Matrix.ofLp_toEuclideanCLM A v) i
    rw [hi, EuclideanSpace.norm_sq_eq]
    have hsum := _root_.norm_sum_le (Finset.univ : Finset (Fin d)) (fun j => A i j * v j)
    simp only [norm_mul] at hsum
    exact (pow_le_pow_left₀ (norm_nonneg _) hsum 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖v j‖))
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ => hf i)
  rw [← EuclideanSpace.norm_sq_eq, ← Finset.sum_mul] at h
  have hh := h.trans (mul_le_mul_of_nonneg_right hs (sq_nonneg ‖v‖))
  nlinarith only [hh, norm_nonneg (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A v), mul_nonneg hK (norm_nonneg v)]

/-- The fixed exponent 3/4 controls every |a| ≤ 3/8. -/
theorem copyCoshCorrection_norm_le_quadratic (d : ℕ) (ρ : ℂ) (hρ : |ρ.re - 1/2| ≤ 3/8) :
    ‖copyCoshCorrection d ρ‖ ≤ (64/9 * Real.sqrt (3/2)) * (d : ℝ) * (ρ.re - 1/2)^2 := by
  let x := integerLogFrequency d
  let a := ρ.re - 1/2
  let θ := |a|/(3/8)
  have hθ0 : 0 ≤ θ := div_nonneg (abs_nonneg _) (by norm_num)
  have hθ1 : θ ≤ 1 := (div_le_one (by norm_num)).mpr hρ
  have hf := coshFrobeniusSquare_eq x (3/8)
  have hprod := finiteIntegerExponentialProduct_le (d := d) (p := (3/4 : ℝ)) (by norm_num) (by norm_num)
  have hbase := exponentialProduct_ge_card_sq x (3/8)
  have hdim : coshFrobeniusSquare x (3/8) ≤ (3/2)*(d : ℝ)^2 := by
    rw [show (2*(3/8) : ℝ) = 3/4 by norm_num] at hf
    change finiteExponentialSum x (3/4)*finiteExponentialSum x (-(3/4)) ≤ (d : ℝ)^2/(1-3/4) at hprod
    have hprod' := hprod.trans_eq (show (d : ℝ)^2 / (1-3/4) = 4*(d : ℝ)^2 by ring)
    linarith only [hf, hprod', hbase]
  let A : Matrix (Fin d) (Fin d) ℂ := fun n m => phase (frequencyGap n m) ρ.im *
    ((Real.cosh (a * frequencyGap n m) : ℂ) - 1)
  have hentry (n m : Fin d) :
      ‖A n m‖ ≤ θ^2 * (Real.cosh ((3/8)*(x n-x m)) - 1) := by
    have hg : frequencyGap n m = x n - x m := rfl
    have h := cosh_sub_one_mul_le_quadratic (x := (3/8)*(x n-x m)) hθ0 hθ1
    have ha : Real.cosh (θ*((3/8)*(x n-x m))) = Real.cosh (a*(x n-x m)) := by
      rw [show θ*((3/8)*(x n-x m)) = |a| *(x n-x m) by dsimp [θ]; ring]
      by_cases h : 0 ≤ a
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h), neg_mul, Real.cosh_neg]
    rw [ha] at h
    dsimp [A]
    rw [norm_mul, phase_norm, one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh _)), hg]
    exact h
  have hsum : (∑ n, ∑ m, ‖A n m‖^2) ≤ θ^4 * coshFrobeniusSquare x (3/8) := by
    unfold coshFrobeniusSquare
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    exact (pow_le_pow_left₀ (norm_nonneg _) (hentry n m) 2).trans_eq (by ring)
  apply euclideanCLM_norm_le_of_sq_sum A (by positivity)
  have hm := hsum.trans (mul_le_mul_of_nonneg_left hdim (pow_nonneg hθ0 _))
  apply hm.trans_eq
  dsimp [θ, a]
  simp only [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/2)]
  rw [show |ρ.re-1/2| ^4 = (ρ.re-1/2)^4 by rw [show 4=2*2 by norm_num, pow_mul, pow_mul, sq_abs]]
  ring

end RiemannResearch.Analysis.ActualZeroPhaseMoments
