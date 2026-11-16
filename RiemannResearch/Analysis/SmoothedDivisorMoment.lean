/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DivisorPolynomialMoment
import RiemannResearch.Analysis.DampedDivisorSeries
import RiemannResearch.Analysis.GeometricL2Series
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Uniform moments of the actual smoothed divisor series

For every positive integer N, the ordinary series
S_N(t) = sum d(n) n^(-1/2-it) exp(-n/N) has a square moment bounded by
C N (1+log N)^4 on every interval of length at most N. The constant is
independent of the interval location, smoothing scale, and truncation.
The difference from the unsmoothed length-N divisor polynomial obeys
the same order of bound. No actual-zeta fourth-moment premise is used.

Source for this contribution to the analytic remainder:
Chourasiya--Simonic, arXiv:2507.15184v2, Section 5.1, equations (53)--(56):
https://arxiv.org/html/2507.15184v2
The block proof uses the project's previously verified finite mean value.
This is a smoothing-defect estimate; it does not estimate the entire
actual zeta-square remainder or establish the required contour identity.
-/
noncomputable section
open MeasureTheory Complex Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis

def divisorMeanValueConstant : ℝ := 12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)

theorem divisorPolynomial_second_moment_le_of_bound {N : ℕ} (hN : 0 < N)
    (w : ℕ → ℂ) {B H T : ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ B) (hHT : H ≤ T) :
    (∫ t in H..T, ‖divisorPolynomial N w t‖ ^ 2) ≤
      divisorMeanValueConstant * (T - H + N) * (B ^ 2 * (1 + Real.log N) ^ 4) := by
  have he : (∑ n ∈ Finset.Icc 1 N, ‖w n * criticalDivisorCoefficient n‖ ^ 2) ≤
      B ^ 2 * (1 + Real.log N) ^ 4 := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, B ^ 2 * ‖criticalDivisorCoefficient n‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hw n hn) 2) (sq_nonneg _)
      _ = B ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖criticalDivisorCoefficient n‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
        simpa using weighted_divisor_coefficient_energy_le N (fun _ => 1) (by simp)
  exact (dirichlet_polynomial_second_moment_window_le N
    (fun n => w n * criticalDivisorCoefficient n) hHT hN).trans
      (mul_le_mul_of_nonneg_left he (by
        have := sub_nonneg.mpr hHT
        positivity))

/-- A genuine block of the exponentially smoothed divisor series. -/
def dampedDivisorBlock (N j : ℕ) (t : ℝ) : ℂ :=
  divisorPolynomial ((j + 1) * N)
    (fun n => if j * N < n then (Real.exp (-(n : ℝ) / N) : ℂ) else 0) t

theorem continuous_dampedDivisorBlock (N j : ℕ) :
    Continuous (dampedDivisorBlock N j) :=
  continuous_divisorPolynomial _ _

theorem exp_neg_nat_le_half_pow (j : ℕ) :
    Real.exp (-(j : ℝ)) ≤ (1 / 2 : ℝ) ^ j := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hi : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he
  calc
    _ = Real.exp (-1) ^ j := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hi j

theorem dampedDivisorBlock_weight_le {N : ℕ} (hN : 0 < N) (j n : ℕ) :
    ‖(if j * N < n then (Real.exp (-(n : ℝ) / N) : ℂ) else 0)‖ ≤ (1 / 2 : ℝ) ^ j := by
  split_ifs with hn
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply le_trans _ (exp_neg_nat_le_half_pow j)
    apply Real.exp_le_exp.mpr
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hjn : (j : ℝ) * N ≤ n := by exact_mod_cast (Nat.le_of_lt hn)
    have hh : (j : ℝ) ≤ (n : ℝ) / N := (le_div_iff₀ hNr).2 hjn
    rw [neg_div]
    exact neg_le_neg hh
  · simp

theorem one_add_log_mul_le (N j : ℕ) (hN : 0 < N) :
    1 + Real.log (((j + 1) * N : ℕ) : ℝ) ≤ (j + 1 : ℝ) * (1 + Real.log N) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hj : (0 : ℝ) < j + 1 := by positivity
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.log_mul (ne_of_gt hj) (ne_of_gt hn0)]
  have hl := Real.log_le_sub_one_of_pos hj
  have hnlog := Real.log_nonneg hn
  nlinarith [mul_nonneg (Nat.cast_nonneg j) hnlog]

/-- Uniform block estimate on every interval of length at most the smoothing scale. -/
theorem dampedDivisorBlock_second_moment_le {N : ℕ} (hN : 0 < N) (j : ℕ)
    {H T : ℝ} (hHT : H ≤ T) (hlen : T - H ≤ N) :
    (∫ t in H..T, ‖dampedDivisorBlock N j t‖ ^ 2) ≤
      divisorMeanValueConstant * N * (1 + Real.log N) ^ 4 *
        ((j + 2 : ℝ) ^ 5 * (1 / 4 : ℝ) ^ j) := by
  have hm : 0 < (j + 1) * N := Nat.mul_pos (by omega) hN
  have hb := divisorPolynomial_second_moment_le_of_bound hm
    (fun n => if j * N<n then (Real.exp (-(n : ℝ) / N) : ℂ) else 0)
    (B := (1 / 2 : ℝ) ^ j)
    (fun n _ => dampedDivisorBlock_weight_le hN j n) hHT
  change (∫ t in H..T, ‖dampedDivisorBlock N j t‖ ^ 2) ≤ _ at hb
  have hl := one_add_log_mul_le N j hN
  have hlog : 0 ≤ 1 + Real.log (((j + 1) * N : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((j + 1) * N : ℕ) := by exact_mod_cast hm
    linarith [Real.log_nonneg h1]
  have hlogN : 0 ≤ 1 + Real.log (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [Real.log_nonneg h1]
  have hlength : T - H + (((j + 1) * N : ℕ) : ℝ) ≤ (j + 2 : ℝ) * N := by
    push_cast
    nlinarith
  have hpow : (1 + Real.log (((j + 1) * N : ℕ) : ℝ)) ^ 4 ≤
      (j + 2 : ℝ) ^ 4 * (1 + Real.log N) ^ 4 := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ hlog
    exact hl.trans (mul_le_mul_of_nonneg_right (by linarith) hlogN)
  have hk : 0 ≤ divisorMeanValueConstant := by unfold divisorMeanValueConstant; positivity
  apply hb.trans
  calc
    _ ≤ divisorMeanValueConstant * ((j + 2 : ℝ) * N) *
        (((1 / 2 : ℝ) ^ j) ^ 2 * ((j + 2 : ℝ) ^ 4 * (1 + Real.log N) ^ 4)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlength hk
      · exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
      · positivity
      · positivity
    _ = _ := by
      rw [← pow_mul, mul_comm j 2, pow_mul]
      norm_num
      ring

theorem norm_dampedDivisorBlock_le {N : ℕ} (hN : 0 < N) (j : ℕ) (t : ℝ) :
    ‖dampedDivisorBlock N j t‖ ≤ (N : ℝ) ^ 2 * ((j + 1 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j) := by
  let M := (j + 1) * N
  have ht (n : ℕ) : ‖Complex.exp (Complex.I * t * (-Real.log n))‖=1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      mul_zero, zero_mul, zero_add, neg_zero, sub_zero, Real.exp_zero]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖((if j * N<n then (Real.exp (-(n : ℝ) / N) : ℂ) else 0) *
        criticalDivisorCoefficient n) * Complex.exp (Complex.I * t * (-Real.log n))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 M, (1 / 2 : ℝ) ^ j * M := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, ht, mul_one, norm_mul]
      exact mul_le_mul (dampedDivisorBlock_weight_le hN j n)
        ((criticalDivisorCoefficient_norm_le n).trans
          (by exact_mod_cast (Finset.mem_Icc.mp hn).2)) (norm_nonneg _) (by positivity)
    _ = _ := by simp [M, Nat.card_Icc]; ring



def smoothedDivisorTerm (N n : ℕ) (t : ℝ) : ℂ :=
  ((Real.exp (-(n : ℝ) / N) : ℂ) * criticalDivisorCoefficient n) *
    Complex.exp (Complex.I * t * (-Real.log n))

def smoothedDivisorSeries (N : ℕ) (t : ℝ) : ℂ :=
  ∑' n, smoothedDivisorTerm N n t

theorem norm_smoothedDivisorTerm_le (N n : ℕ) (t : ℝ) :
    ‖smoothedDivisorTerm N n t‖ ≤ (n : ℝ) * Real.exp (-(n : ℝ) / N) := by
  have ht : ‖Complex.exp (Complex.I * t * (-Real.log n))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      mul_zero, zero_mul, zero_add, neg_zero, sub_zero, Real.exp_zero]
  unfold smoothedDivisorTerm
  rw [norm_mul, ht, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (criticalDivisorCoefficient_norm_le n) (Real.exp_pos (-(n : ℝ) / N)).le

theorem summable_smoothedDivisorTerm_majorant {N : ℕ} (hN : 0 < N) :
    Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : ‖Real.exp (-1 / (N : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num) hN0
  have he (n : ℕ) : Real.exp (-(n : ℝ) / N) = Real.exp (-1 / (N : ℝ)) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [pow_one, he] using
    summable_pow_mul_geometric_of_norm_lt_one (r := Real.exp (-1 / (N : ℝ))) 1 hq

theorem summable_smoothedDivisorTerm {N : ℕ} (hN : 0 < N) (t : ℝ) :
    Summable (fun n => smoothedDivisorTerm N n t) :=
  Summable.of_norm_bounded (summable_smoothedDivisorTerm_majorant hN)
    (fun n => norm_smoothedDivisorTerm_le N n t)

/-- The integer-scale moment provider and the real-scale convergence provider
use exactly the same ordinary divisor series. -/
theorem smoothedDivisorSeries_eq_dampedDivisorSeries {N : ℕ} (hN : 0 < N) (t : ℝ) :
    smoothedDivisorSeries N t = dampedDivisorSeries (N : ℝ) t := by
  have hz : smoothedDivisorTerm N 0 t = 0 := by
    simp [smoothedDivisorTerm, criticalDivisorCoefficient]
  unfold smoothedDivisorSeries
  rw [(summable_smoothedDivisorTerm hN t).tsum_eq_zero_add, hz, zero_add]
  rfl

theorem continuous_smoothedDivisorSeries {N : ℕ} (hN : 0 < N) :
    Continuous (smoothedDivisorSeries N) := by
  apply continuous_tsum (fun n => by unfold smoothedDivisorTerm; fun_prop)
    (summable_smoothedDivisorTerm_majorant hN)
  exact norm_smoothedDivisorTerm_le N

theorem dampedDivisorBlock_eq_sum_Ioc (N j : ℕ) (t : ℝ) :
    dampedDivisorBlock N j t =
      ∑ n ∈ Finset.Ioc (j * N) ((j + 1) * N), smoothedDivisorTerm N n t := by
  unfold dampedDivisorBlock divisorPolynomial
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hset : (Finset.Icc 1 ((j + 1) * N)).filter (fun n => j * N<n) =
      Finset.Ioc (j * N) ((j + 1) * N) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  rfl

/-- Exact partition; all finite coefficients and phases are retained. -/
theorem sum_dampedDivisorBlock_eq (N J : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range J, dampedDivisorBlock N j t) =
      ∑ n ∈ Finset.Ioc 0 (J * N), smoothedDivisorTerm N n t := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, dampedDivisorBlock_eq_sum_Ioc]
    exact Finset.sum_Ioc_consecutive _ (Nat.zero_le _)
      (Nat.mul_le_mul_right N (Nat.le_succ J))

theorem summable_dampedDivisorBlock_majorant (N : ℕ) :
    Summable (fun j : ℕ => (N : ℝ) ^ 2 * ((j + 1 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j)) := by
  have h : Summable (fun j : ℕ => (j + 1 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j) := by
    simpa only [Nat.cast_one] using
      Real.summable_shifted_pow_mul_geometric (q := (1 / 2 : ℝ))
        (by norm_num) (by norm_num) 2 1
  exact h.mul_left ((N : ℝ) ^ 2)

theorem summable_dampedDivisorBlock {N : ℕ} (hN : 0 < N) (t : ℝ) :
    Summable (fun j => dampedDivisorBlock N j t) :=
  Summable.of_norm_bounded (summable_dampedDivisorBlock_majorant N)
    (fun j => norm_dampedDivisorBlock_le hN j t)

/-- The block sum is the ordinary actual divisor series, with no summation convention assumed. -/
theorem smoothedDivisorSeries_eq_tsum_blocks {N : ℕ} (hN : 0 < N) (t : ℝ) :
    smoothedDivisorSeries N t = ∑' j, dampedDivisorBlock N j t := by
  have hindex : Tendsto (fun J : ℕ => J * N + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with J hJ
    have := Nat.le_mul_of_pos_right J hN
    omega
  have hlim := ((summable_smoothedDivisorTerm hN t).hasSum.tendsto_sum_nat).comp hindex
  have he (J : ℕ) : (∑ n ∈ Finset.range (J * N + 1), smoothedDivisorTerm N n t) =
      ∑ j ∈ Finset.range J, dampedDivisorBlock N j t := by
    rw [sum_dampedDivisorBlock_eq]
    have hs : Finset.range (J * N + 1) = insert 0 (Finset.Ioc 0 (J * N)) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [hs, Finset.sum_insert (by simp)]
    simp [smoothedDivisorTerm, criticalDivisorCoefficient]
  simp only [Function.comp_def, he] at hlim
  exact tendsto_nhds_unique hlim (summable_dampedDivisorBlock hN t).hasSum.tendsto_sum_nat

/-- One constant for all smoothing scales, cutoffs, and interval translations. -/
def smoothedDivisorMomentConstant : ℝ :=
  2 * divisorMeanValueConstant * (∑' j : ℕ, (j + 2 : ℝ) ^ 5 * (9 / 16 : ℝ) ^ j)

theorem smoothedDivisorSeries_second_moment_le {N : ℕ} (hN : 0 < N)
    {H T : ℝ} (hHT : H ≤ T) (hlen : T - H ≤ N) :
    (∫ t in H..T, ‖smoothedDivisorSeries N t‖ ^ 2) ≤
      smoothedDivisorMomentConstant * N * (1 + Real.log N) ^ 4 := by
  have hb := Complex.integral_norm_tsum_sq_le_geometric
    (dampedDivisorBlock N)
    (fun j => (N : ℝ) ^ 2 * ((j + 1 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j))
    (continuous_dampedDivisorBlock N) (summable_dampedDivisorBlock_majorant N)
    (norm_dampedDivisorBlock_le hN) hHT
    (A := divisorMeanValueConstant * N * (1 + Real.log N) ^ 4)
    (by unfold divisorMeanValueConstant; positivity) 5
    (fun j => dampedDivisorBlock_second_moment_le hN j hHT hlen)
  simp_rw [← smoothedDivisorSeries_eq_tsum_blocks hN] at hb
  convert hb using 1
  unfold smoothedDivisorMomentConstant
  ring

def divisorSmoothingDefect (N : ℕ) (t : ℝ) : ℂ :=
  smoothedDivisorSeries N t - divisorPolynomial N (fun _ => 1) t

theorem smoothedDivisorSeries_eq_polynomial_add_defect (N : ℕ) (t : ℝ) :
    smoothedDivisorSeries N t =
      divisorPolynomial N (fun _ => 1) t + divisorSmoothingDefect N t := by
  unfold divisorSmoothingDefect
  ring

/-- The entire smoothing defect has a uniform moment bound, without a zeta-moment premise. -/
theorem divisorSmoothingDefect_second_moment_le {N : ℕ} (hN : 0 < N)
    {H T : ℝ} (hHT : H ≤ T) (hlen : T - H ≤ N) :
    (∫ t in H..T, ‖divisorSmoothingDefect N t‖ ^ 2) ≤
      (2 * smoothedDivisorMomentConstant + 4 * divisorMeanValueConstant) *
        N * (1 + Real.log N) ^ 4 := by
  have hS := continuous_smoothedDivisorSeries hN
  have hP := continuous_divisorPolynomial N (fun _ => 1)
  have hle : (∫ t in H..T, ‖divisorSmoothingDefect N t‖ ^ 2) ≤
      2 * ((∫ t in H..T, ‖smoothedDivisorSeries N t‖ ^ 2) +
        ∫ t in H..T, ‖divisorPolynomial N (fun _ => 1) t‖ ^ 2) := by
    calc
      _ ≤ ∫ t in H..T, 2 * (‖smoothedDivisorSeries N t‖ ^ 2 +
          ‖divisorPolynomial N (fun _ => 1) t‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on hHT
          ((hS.sub hP).norm.pow 2 |>.intervalIntegrable H T)
          (((hS.norm.pow 2).add (hP.norm.pow 2)).const_mul 2 |>.intervalIntegrable H T)
        intro t ht
        have hn := norm_sub_le (smoothedDivisorSeries N t) (divisorPolynomial N (fun _ => 1) t)
        have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
        dsimp [divisorSmoothingDefect]
        nlinarith [sq_nonneg (‖smoothedDivisorSeries N t‖ - ‖divisorPolynomial N (fun _ => 1) t‖)]
      _ = _ := by
        have hiS : IntervalIntegrable (fun t => ‖smoothedDivisorSeries N t‖ ^ 2) volume H T :=
          (hS.norm.pow 2).intervalIntegrable H T
        have hiP : IntervalIntegrable
            (fun t => ‖divisorPolynomial N (fun _ => 1) t‖ ^ 2) volume H T :=
          (hP.norm.pow 2).intervalIntegrable H T
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hiS hiP]
  have hmS := smoothedDivisorSeries_second_moment_le hN hHT hlen
  have hmP := divisorPolynomial_second_moment_le hN (fun _ => 1) (by simp) hHT
  change (∫ t in H..T, ‖divisorPolynomial N (fun _ => 1) t‖ ^ 2) ≤
    divisorMeanValueConstant * (T - H + N) * (1 + Real.log N) ^ 4 at hmP
  have hk : 0 ≤ divisorMeanValueConstant := by unfold divisorMeanValueConstant; positivity
  have hmP' : (∫ t in H..T, ‖divisorPolynomial N (fun _ => 1) t‖ ^ 2) ≤
      2 * divisorMeanValueConstant * N * (1 + Real.log N) ^ 4 := by
    apply hmP.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : T - H + N ≤ 2 * N) hk)
      (by positivity : 0 ≤ (1 + Real.log N) ^ 4)
    nlinarith [hh]
  nlinarith
end RiemannResearch.Analysis
