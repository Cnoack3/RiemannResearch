/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import RiemannResearch.Analysis.SmoothedDivisorMoment
import RiemannResearch.Analysis.DivisorLSeries

/-!
# Weighted divisor mean values

Unconditional translated-window estimates for the divisor head on the line
`re s = 1/4` and the divisor tail on the line `re s = 5/4`.
The tail is assembled from exact base-16 shells, retaining the decay in the
coefficient weights before applying the finite divisor mean-value theorem.
-/

open Filter MeasureTheory Complex Set
open scoped BigOperators

noncomputable section
namespace RiemannResearch.Analysis

/-- The finite divisor head on the line of real part one quarter. -/
def quarterDivisorHead (N : ℕ) (t : ℝ) : ℂ :=
  divisorPolynomial N (fun n => (((n : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ)) t

/-- The strongest interval form of the finite weighted-head estimate. -/
theorem quarterDivisorHead_second_moment_le {N : ℕ} (hN : 0 < N)
    {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖quarterDivisorHead N t‖ ^ 2) ≤
      divisorMeanValueConstant * (T - H + N) *
        ((N : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log N) ^ 4) := by
  have h := divisorPolynomial_second_moment_le_of_bound hN
    (fun n => (((n : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ))
    (B := (N : ℝ) ^ (1 / 4 : ℝ)) (H := H) (T := T) (by
      intro n hn
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by
        exact_mod_cast (Finset.mem_Icc.mp hn).2) (by norm_num)) hHT
  have hp : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  simpa only [quarterDivisorHead, hp] using h

/-- Cauchy--Schwarz and the proved logarithmic coefficient energy give a
pointwise estimate for arbitrary bounded weights. -/
theorem divisorPolynomial_norm_sq_le_of_bound (N : ℕ) (w : ℕ → ℂ)
    {B : ℝ} (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ B) (t : ℝ) :
    ‖divisorPolynomial N w t‖ ^ 2 ≤
      (N : ℝ) * (B ^ 2 * (1 + Real.log N) ^ 4) := by
  have hp (n : ℕ) : ‖Complex.exp (I * t * (-Real.log n))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      mul_zero, zero_mul, zero_add, neg_zero, sub_zero, Real.exp_zero]
  have hn : ‖divisorPolynomial N w t‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ‖w n * criticalDivisorCoefficient n‖ := by
    unfold divisorPolynomial
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N,
          ‖(w n * criticalDivisorCoefficient n) *
            Complex.exp (I * t * (-Real.log n))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, hp, mul_one]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
    (fun _ : ℕ => (1 : ℝ)) (fun n => ‖w n * criticalDivisorCoefficient n‖)
  have hc' : (∑ n ∈ Finset.Icc 1 N, ‖w n * criticalDivisorCoefficient n‖) ^ 2 ≤
      (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖w n * criticalDivisorCoefficient n‖ ^ 2 := by
    simpa using hc
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hc'.trans
    (mul_le_mul_of_nonneg_left
      (weighted_divisor_coefficient_energy_le_mul N w hw) (Nat.cast_nonneg N)))

/-- The exact base-16 divisor shell on the line of real part five quarters. -/
def fiveQuarterDivisorBlock (N j : ℕ) (t : ℝ) : ℂ :=
  divisorPolynomial (16 ^ (j + 1) * N)
    (fun n => if 16 ^ j * N < n then (((n : ℝ) ^ (-3 / 4 : ℝ) : ℝ) : ℂ) else 0) t

theorem continuous_fiveQuarterDivisorBlock (N j : ℕ) :
    Continuous (fiveQuarterDivisorBlock N j) :=
  continuous_divisorPolynomial _ _

private theorem rpow_square (x a : ℝ) (hx : 0 ≤ x) :
    (x ^ a) ^ 2 = x ^ (a * 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem sixteen_rpow_neg_three_quarters :
    (16 : ℝ) ^ (-3 / 4 : ℝ) = 1 / 8 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
    ← Real.rpow_natCast_mul (by norm_num)]
  norm_num [Real.rpow_neg, Real.rpow_natCast]

private theorem geometric_tail_weight {N : ℕ} (hN : 0 < N) (j : ℕ) :
    ((16 ^ j * N : ℕ) : ℝ) ^ (-3 / 4 : ℝ) =
      (1 / 8 : ℝ) ^ j * (N : ℝ) ^ (-3 / 4 : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul (by norm_num), mul_comm (j : ℝ),
    Real.rpow_mul (by norm_num), Real.rpow_natCast,
    sixteen_rpow_neg_three_quarters]

private theorem geometric_tail_weight_sq {N : ℕ} (hN : 0 < N) (j : ℕ) :
    (((16 ^ j * N : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ^ 2 =
      (1 / 64 : ℝ) ^ j * (N : ℝ) ^ (-3 / 2 : ℝ) := by
  rw [geometric_tail_weight hN, mul_pow, rpow_square _ _ (Nat.cast_nonneg _)]
  norm_num only [show (-3 / 4 : ℝ) * 2 = -3 / 2 by norm_num]
  rw [← pow_mul, mul_comm j 2, pow_mul]
  norm_num

theorem fiveQuarterDivisorBlock_weight_le {N : ℕ} (hN : 0 < N)
    (j n : ℕ) :
    ‖(if 16 ^ j * N < n then (((n : ℝ) ^ (-3 / 4 : ℝ) : ℝ) : ℂ) else 0)‖ ≤
      ((16 ^ j * N : ℕ) : ℝ) ^ (-3 / 4 : ℝ) := by
  split_ifs with hn
  · rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · exact_mod_cast hn.le
    · norm_num
  · simpa only [norm_zero] using Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem geometric_tail_log_bound {N : ℕ} (hN : 0 < N) (j : ℕ) :
    1 + Real.log ((16 ^ (j + 1) * N : ℕ) : ℝ) ≤
      (j + 2 : ℝ) * (1 + Real.log 16) * (1 + Real.log N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN := Real.log_nonneg hN1
  have hlog16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow]
  push_cast
  calc
    _ ≤ (j + 2 : ℝ) * (1 + Real.log 16 + Real.log N) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg j) hlogN]
    _ ≤ (j + 2 : ℝ) * ((1 + Real.log 16) * (1 + Real.log N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hlog16 hlogN]
    _ = _ := by ring

/-- The polynomial factor shared by both pointwise and mean-square shell
bounds. It displays the full decay in the starting cutoff. -/
def fiveQuarterDivisorTailScale (N : ℕ) : ℝ :=
  (1 + Real.log 16) ^ 4 * (N : ℝ) ^ (-3 / 2 : ℝ) *
    (1 + Real.log N) ^ 4

theorem fiveQuarterDivisorTailScale_nonneg (N : ℕ) :
    0 ≤ fiveQuarterDivisorTailScale N := by
  unfold fiveQuarterDivisorTailScale
  positivity

private theorem geometric_divisor_tail_energy_bound {N : ℕ} (hN : 0 < N)
    (j : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    (D + ((16 ^ (j + 1) * N : ℕ) : ℝ)) *
        ((((16 ^ j * N : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ^ 2 *
          (1 + Real.log ((16 ^ (j + 1) * N : ℕ) : ℝ)) ^ 4) ≤
      (D + 16 * N) * fiveQuarterDivisorTailScale N *
        ((j + 2 : ℝ) ^ 4 * (1 / 4 : ℝ) ^ j) := by
  have hgeo : (1 : ℝ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
  have hlength : D + ((16 ^ (j + 1) * N : ℕ) : ℝ) ≤
      (16 : ℝ) ^ j * (D + 16 * N) := by
    push_cast
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hgeo hD]
  have hM : 0 < 16 ^ (j + 1) * N := by positivity
  have hlog : 0 ≤ 1 + Real.log ((16 ^ (j + 1) * N : ℕ) : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ((16 ^ (j + 1) * N : ℕ) : ℝ) by
      exact_mod_cast hM)
    linarith
  have hlog4 : (1 + Real.log ((16 ^ (j + 1) * N : ℕ) : ℝ)) ^ 4 ≤
      (j + 2 : ℝ) ^ 4 * (1 + Real.log 16) ^ 4 * (1 + Real.log N) ^ 4 := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ hlog (geometric_tail_log_bound hN j) 4
  calc
    _ ≤ ((16 : ℝ) ^ j * (D + 16 * N)) *
        ((((16 ^ j * N : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ^ 2 *
          (1 + Real.log ((16 ^ (j + 1) * N : ℕ) : ℝ)) ^ 4) :=
      mul_le_mul_of_nonneg_right hlength (by positivity)
    _ ≤ ((16 : ℝ) ^ j * (D + 16 * N)) *
        ((((16 ^ j * N : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ^ 2 *
          ((j + 2 : ℝ) ^ 4 * (1 + Real.log 16) ^ 4 * (1 + Real.log N) ^ 4)) := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlog4 (sq_nonneg _)) (by positivity)
    _ = _ := by
      rw [geometric_tail_weight_sq hN]
      have hq : (16 : ℝ) ^ j * (1 / 64 : ℝ) ^ j = (1 / 4 : ℝ) ^ j := by
        rw [← mul_pow]
        norm_num
      unfold fiveQuarterDivisorTailScale
      calc
        _ = ((16 : ℝ) ^ j * (1 / 64 : ℝ) ^ j) *
          ((D + 16 * N) * (1 + Real.log 16) ^ 4 *
            (N : ℝ) ^ (-3 / 2 : ℝ) * (1 + Real.log N) ^ 4 * (j + 2 : ℝ) ^ 4) := by ring
        _ = _ := by rw [hq]; ring

/-- Exact geometric decay of the actual finite tail shells on every
translated interval, with no restriction on the interval's location or length. -/
theorem fiveQuarterDivisorBlock_second_moment_le {N : ℕ} (hN : 0 < N)
    (j : ℕ) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖fiveQuarterDivisorBlock N j t‖ ^ 2) ≤
      (divisorMeanValueConstant * (T - H + 16 * N) * fiveQuarterDivisorTailScale N) *
        ((j + 2 : ℝ) ^ 4 * (1 / 4 : ℝ) ^ j) := by
  have hM : 0 < 16 ^ (j + 1) * N := by positivity
  have hm := divisorPolynomial_second_moment_le_of_bound hM
    (fun n => if 16 ^ j * N < n then (((n : ℝ) ^ (-3 / 4 : ℝ) : ℝ) : ℂ) else 0)
    (fun n _ => fiveQuarterDivisorBlock_weight_le hN j n) hHT
  change (∫ t in H..T, ‖fiveQuarterDivisorBlock N j t‖ ^ 2) ≤ _ at hm
  have he := mul_le_mul_of_nonneg_left
    (geometric_divisor_tail_energy_bound hN j (sub_nonneg.mpr hHT))
    (show 0 ≤ divisorMeanValueConstant by unfold divisorMeanValueConstant; positivity)
  exact hm.trans (by simpa only [mul_assoc] using he)

/-- A uniform summable majorant of the actual tail shells. -/
theorem norm_fiveQuarterDivisorBlock_le {N : ℕ} (hN : 0 < N) (j : ℕ) (t : ℝ) :
    ‖fiveQuarterDivisorBlock N j t‖ ≤
      Real.sqrt (16 * N * fiveQuarterDivisorTailScale N) *
        ((j + 2 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j) := by
  have hm := divisorPolynomial_norm_sq_le_of_bound (16 ^ (j + 1) * N)
    (fun n => if 16 ^ j * N < n then (((n : ℝ) ^ (-3 / 4 : ℝ) : ℝ) : ℂ) else 0)
    (fun n _ => fiveQuarterDivisorBlock_weight_le hN j n) t
  change ‖fiveQuarterDivisorBlock N j t‖ ^ 2 ≤ _ at hm
  have he := geometric_divisor_tail_energy_bound hN j (D := 0) le_rfl
  simp only [zero_add] at he
  have hb : 0 ≤ 16 * (N : ℝ) * fiveQuarterDivisorTailScale N :=
    mul_nonneg (by positivity) (fiveQuarterDivisorTailScale_nonneg N)
  have hsq : (Real.sqrt (16 * N * fiveQuarterDivisorTailScale N) *
      ((j + 2 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j)) ^ 2 =
      (16 * N * fiveQuarterDivisorTailScale N) *
        ((j + 2 : ℝ) ^ 4 * (1 / 4 : ℝ) ^ j) := by
    have hq : ((1 / 2 : ℝ) ^ j) ^ 2 = (1 / 4 : ℝ) ^ j := by
      rw [← pow_mul, mul_comm j 2, pow_mul]
      norm_num
    rw [mul_pow, Real.sq_sqrt hb, mul_pow, hq, ← pow_mul]
  have hmain := hm.trans he
  rw [← hsq] at hmain
  have hnonneg : 0 ≤ Real.sqrt (16 * N * fiveQuarterDivisorTailScale N) *
      ((j + 2 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j) := by positivity
  nlinarith [norm_nonneg (fiveQuarterDivisorBlock N j t)]

theorem summable_fiveQuarterDivisorBlock {N : ℕ} (hN : 0 < N) (t : ℝ) :
    Summable (fun j => fiveQuarterDivisorBlock N j t) := by
  exact Summable.of_norm_bounded
    ((Real.summable_shifted_pow_mul_geometric (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) 2 2).mul_left
        (Real.sqrt (16 * N * fiveQuarterDivisorTailScale N)))
    (fun j => norm_fiveQuarterDivisorBlock_le hN j t)

/-- A shifted divisor term with its real power and oscillatory phase explicit. -/
def powerWeightedDivisorTerm (a : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ((((n : ℝ) ^ a : ℝ) : ℂ) * criticalDivisorCoefficient n) *
    Complex.exp (I * t * (-Real.log n))

theorem powerWeightedDivisorTerm_eq_div {n : ℕ} (hn : 0 < n) (a t : ℝ) :
    powerWeightedDivisorTerm a n t =
      (ArithmeticFunction.sigma 0 n : ℂ) /
        (n : ℂ) ^ (((1 / 2 - a : ℝ) : ℂ) + I * t) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  unfold powerWeightedDivisorTerm criticalDivisorCoefficient
  rw [Real.rpow_def_of_pos hnr, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero hnz, hl]
  simp only [div_eq_mul_inv]
  rw [← Complex.exp_neg]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_inv]
  calc
    _ = (ArithmeticFunction.sigma 0 n : ℂ) *
        (Complex.exp ((Real.log n : ℂ) * a) *
          Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ)) *
          Complex.exp (I * t * (-(Real.log n : ℂ)))) := by ring
    _ = (ArithmeticFunction.sigma 0 n : ℂ) *
        Complex.exp ((Real.log n : ℂ) * a +
          -(1 / 2 : ℂ) * (Real.log n : ℂ) + I * t * (-(Real.log n : ℂ))) := by
      rw [Complex.exp_add, Complex.exp_add]
    _ = _ := by congr 2 <;> ring

theorem powerWeightedDivisorTerm_eq_LSeries_term (a t : ℝ) (n : ℕ) :
    powerWeightedDivisorTerm a n t =
      LSeries.term (fun n => (ArithmeticFunction.sigma 0 n : ℂ))
        (((1 / 2 - a : ℝ) : ℂ) + I * t) n := by
  by_cases hn : n = 0
  · subst n
    simp [powerWeightedDivisorTerm, criticalDivisorCoefficient, LSeries.term_def]
  · rw [LSeries.term_def, if_neg hn]
    exact powerWeightedDivisorTerm_eq_div (Nat.pos_of_ne_zero hn) a t

/-- Absolute convergence is proved for the ordinary actual divisor terms. -/
theorem summable_fiveQuarterDivisorTerm (t : ℝ) :
    Summable (fun n => powerWeightedDivisorTerm (-3 / 4) n t) := by
  have hs := divisorLSeriesSummable
    (s := (((1 / 2 - (-3 / 4) : ℝ) : ℂ) + I * t)) (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im]
      norm_num)
  change Summable (LSeries.term (fun n => (ArithmeticFunction.sigma 0 n : ℂ))
    (((1 / 2 - (-3 / 4) : ℝ) : ℂ) + I * t)) at hs
  exact hs.congr (fun n => (powerWeightedDivisorTerm_eq_LSeries_term (-3 / 4) t n).symm)

/-- The ordinary unsmoothed divisor tail on the line of real part five quarters. -/
def fiveQuarterDivisorTail (N : ℕ) (t : ℝ) : ℂ :=
  ∑' n, if N < n then powerWeightedDivisorTerm (-3 / 4) n t else 0

theorem summable_fiveQuarterDivisorTailTerm (N : ℕ) (t : ℝ) :
    Summable (fun n => if N < n then powerWeightedDivisorTerm (-3 / 4) n t else 0) := by
  have hi := (summable_fiveQuarterDivisorTerm t).indicator (Set.Ioi N)
  apply hi.congr
  intro n
  by_cases hn : N < n
  · rw [Set.indicator_of_mem (s := Set.Ioi N) hn, if_pos hn]
  · rw [Set.indicator_of_notMem (s := Set.Ioi N) hn, if_neg hn]

theorem fiveQuarterDivisorBlock_eq_sum_Ioc (N j : ℕ) (t : ℝ) :
    fiveQuarterDivisorBlock N j t =
      ∑ n ∈ Finset.Ioc (16 ^ j * N) (16 ^ (j + 1) * N),
        powerWeightedDivisorTerm (-3 / 4) n t := by
  unfold fiveQuarterDivisorBlock divisorPolynomial
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hs : (Finset.Icc 1 (16 ^ (j + 1) * N)).filter (fun n => 16 ^ j * N < n) =
      Finset.Ioc (16 ^ j * N) (16 ^ (j + 1) * N) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hs]
  rfl

/-- Exact finite partition into geometric shells. -/
theorem sum_fiveQuarterDivisorBlock_eq (N J : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range J, fiveQuarterDivisorBlock N j t) =
      ∑ n ∈ Finset.Ioc N (16 ^ J * N), powerWeightedDivisorTerm (-3 / 4) n t := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, fiveQuarterDivisorBlock_eq_sum_Ioc]
    apply Finset.sum_Ioc_consecutive
    · exact Nat.le_mul_of_pos_left N (pow_pos (by decide) J)
    · apply Nat.mul_le_mul_right
      rw [pow_succ]
      omega

/-- The geometric construction equals the ordinary absolutely convergent
tail, with all divisor coefficients retained exactly. -/
theorem fiveQuarterDivisorTail_eq_tsum_blocks {N : ℕ} (hN : 0 < N) (t : ℝ) :
    fiveQuarterDivisorTail N t = ∑' j, fiveQuarterDivisorBlock N j t := by
  have hpow (J : ℕ) : J ≤ 16 ^ J := by
    induction J with
    | zero => norm_num
    | succ J ih =>
      rw [pow_succ]
      have hp : 0 < 16 ^ J := pow_pos (by decide) J
      omega
  have hindex : Tendsto (fun J : ℕ => 16 ^ J * N + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with J hJ
    have hp := hpow J
    have hm := Nat.le_mul_of_pos_right (16 ^ J) hN
    omega
  have hlim := (summable_fiveQuarterDivisorTailTerm N t).hasSum.tendsto_sum_nat.comp hindex
  have he (J : ℕ) :
      (∑ n ∈ Finset.range (16 ^ J * N + 1),
        if N < n then powerWeightedDivisorTerm (-3 / 4) n t else 0) =
      ∑ j ∈ Finset.range J, fiveQuarterDivisorBlock N j t := by
    rw [sum_fiveQuarterDivisorBlock_eq, ← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  simp only [Function.comp_def, he] at hlim
  exact tendsto_nhds_unique hlim
    (summable_fiveQuarterDivisorBlock hN t).hasSum.tendsto_sum_nat

theorem summable_fiveQuarterDivisorBlock_majorant (N : ℕ) :
    Summable (fun j : ℕ => Real.sqrt (16 * N * fiveQuarterDivisorTailScale N) *
      ((j + 2 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j)) := by
  exact (Real.summable_shifted_pow_mul_geometric
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) 2 2).mul_left _

theorem continuous_fiveQuarterDivisorTail {N : ℕ} (hN : 0 < N) :
    Continuous (fiveQuarterDivisorTail N) := by
  have he : fiveQuarterDivisorTail N = fun t => ∑' j, fiveQuarterDivisorBlock N j t :=
    funext (fiveQuarterDivisorTail_eq_tsum_blocks hN)
  rw [he]
  exact continuous_tsum (continuous_fiveQuarterDivisorBlock N)
    (summable_fiveQuarterDivisorBlock_majorant N) (norm_fiveQuarterDivisorBlock_le hN)

/-- A single explicit finite constant for every cutoff and every interval. -/
def fiveQuarterDivisorMomentConstant : ℝ :=
  2 * divisorMeanValueConstant * (1 + Real.log 16) ^ 4 *
    (∑' j : ℕ, (j + 2 : ℝ) ^ 4 * (9 / 16 : ℝ) ^ j)

theorem fiveQuarterDivisorMomentConstant_nonneg :
    0 ≤ fiveQuarterDivisorMomentConstant := by
  unfold fiveQuarterDivisorMomentConstant
  apply mul_nonneg
  · unfold divisorMeanValueConstant
    positivity
  · exact tsum_nonneg (fun j => by positivity)

/-- Unconditional mean-square bound for the actual ordinary divisor tail.
The interval may have arbitrary length and arbitrary translation. -/
theorem fiveQuarterDivisorTail_second_moment_le {N : ℕ} (hN : 0 < N)
    {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖fiveQuarterDivisorTail N t‖ ^ 2) ≤
      fiveQuarterDivisorMomentConstant * (T - H + 16 * N) *
        (N : ℝ) ^ (-3 / 2 : ℝ) * (1 + Real.log N) ^ 4 := by
  have hA : 0 ≤ divisorMeanValueConstant * (T - H + 16 * N) *
      fiveQuarterDivisorTailScale N := by
    apply mul_nonneg
    · have := sub_nonneg.mpr hHT
      unfold divisorMeanValueConstant
      positivity
    · exact fiveQuarterDivisorTailScale_nonneg N
  have hb := Complex.integral_norm_tsum_sq_le_geometric
    (fiveQuarterDivisorBlock N)
    (fun j => Real.sqrt (16 * N * fiveQuarterDivisorTailScale N) *
      ((j + 2 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j))
    (continuous_fiveQuarterDivisorBlock N) (summable_fiveQuarterDivisorBlock_majorant N)
    (norm_fiveQuarterDivisorBlock_le hN) hHT hA 4
    (fun j => fiveQuarterDivisorBlock_second_moment_le hN j hHT)
  simp_rw [← fiveQuarterDivisorTail_eq_tsum_blocks hN] at hb
  convert hb using 1
  unfold fiveQuarterDivisorMomentConstant fiveQuarterDivisorTailScale
  ring

/-- On a window of length at most twice the cutoff the actual tail has the
required `N^(-1/2) log^4 N` moment, with no zeta-moment premise. -/
theorem fiveQuarterDivisorTail_second_moment_le_short {N : ℕ} (hN : 0 < N)
    {H T : ℝ} (hHT : H ≤ T) (hlen : T - H ≤ 2 * N) :
    (∫ t in H..T, ‖fiveQuarterDivisorTail N t‖ ^ 2) ≤
      (18 * fiveQuarterDivisorMomentConstant) *
        (N : ℝ) ^ (-1 / 2 : ℝ) * (1 + Real.log N) ^ 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : (N : ℝ) * (N : ℝ) ^ (-3 / 2 : ℝ) = (N : ℝ) ^ (-1 / 2 : ℝ) := by
    calc
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-3 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + (-3 / 2 : ℝ)) := (Real.rpow_add hN0 _ _).symm
      _ = _ := by norm_num
  calc
    _ ≤ fiveQuarterDivisorMomentConstant * (T - H + 16 * N) *
        (N : ℝ) ^ (-3 / 2 : ℝ) * (1 + Real.log N) ^ 4 :=
      fiveQuarterDivisorTail_second_moment_le hN hHT
    _ ≤ fiveQuarterDivisorMomentConstant * (18 * N) *
        (N : ℝ) ^ (-3 / 2 : ℝ) * (1 + Real.log N) ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      exact mul_le_mul_of_nonneg_left (by linarith) fiveQuarterDivisorMomentConstant_nonneg
    _ = _ := by
      calc
        _ = (18 * fiveQuarterDivisorMomentConstant) *
          ((N : ℝ) * (N : ℝ) ^ (-3 / 2 : ℝ)) * (1 + Real.log N) ^ 4 := by ring
        _ = _ := by rw [hp]

/-- Every finite divisor polynomial admits an ordinate-independent bound. -/
theorem divisorPolynomial_uniform_bound (N : ℕ) (w : ℕ → ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ‖divisorPolynomial N w t‖ ≤ D := by
  refine ⟨∑ n ∈ Finset.Icc 1 N, ‖w n * criticalDivisorCoefficient n‖,
    Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro t
  have hp (n : ℕ) : ‖Complex.exp (I * t * (-Real.log n))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      mul_zero, zero_mul, zero_add, neg_zero, sub_zero, Real.exp_zero]
  unfold divisorPolynomial
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
      ‖(w n * criticalDivisorCoefficient n) * Complex.exp (I * t * (-Real.log n))‖ :=
        norm_sum_le _ _
    _ = _ := by simp only [norm_mul, hp, mul_one]

theorem quarterDivisorHead_uniform_bound (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ‖quarterDivisorHead N t‖ ≤ D :=
  divisorPolynomial_uniform_bound N _

theorem continuous_quarterDivisorHead (N : ℕ) :
    Continuous (quarterDivisorHead N) :=
  continuous_divisorPolynomial N _

/-- Absolute geometric control provides a uniform pointwise bound for the
actual ordinary tail, independent of the ordinate. -/
theorem fiveQuarterDivisorTail_uniform_bound {N : ℕ} (hN : 0 < N) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ‖fiveQuarterDivisorTail N t‖ ≤ D := by
  let b : ℕ → ℝ := fun j =>
    Real.sqrt (16 * N * fiveQuarterDivisorTailScale N) *
      ((j + 2 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j)
  have hb : Summable b := summable_fiveQuarterDivisorBlock_majorant N
  refine ⟨∑' j, b j, tsum_nonneg (fun j => by dsimp [b]; positivity), ?_⟩
  intro t
  have hn : Summable (fun j => ‖fiveQuarterDivisorBlock N j t‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => norm_fiveQuarterDivisorBlock_le hN j t) hb
  rw [fiveQuarterDivisorTail_eq_tsum_blocks hN]
  exact (norm_tsum_le_tsum_norm hn).trans
    (Summable.tsum_le_tsum (fun j => norm_fiveQuarterDivisorBlock_le hN j t) hn hb)

end RiemannResearch.Analysis
