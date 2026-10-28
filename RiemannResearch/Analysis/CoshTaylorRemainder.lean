/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
/-!
# Positive tails of the real cosh Taylor series

The exact convergent tail is retained before its nonnegative majorants.
The comparison-frequency estimate controls every finite Taylor order.
Concrete consumer: actual zeta-zero horizontal-moment expansions.
These are elementary deductions from Mathlib's cosh power series; no
analytic-number-theory hypothesis or novelty claim is involved.
-/

noncomputable section
open scoped BigOperators
namespace Real
def coshTaylorTerm (x : ℝ) (k : ℕ) : ℝ :=
  x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)
def coshTaylorHead (J : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (J + 1), coshTaylorTerm x k
def coshTaylorRemainder (J : ℕ) (x : ℝ) : ℝ :=
  Real.cosh x - coshTaylorHead J x
theorem coshTaylorTerm_nonneg (x : ℝ) (k : ℕ) :
    0 ≤ coshTaylorTerm x k := by
  unfold coshTaylorTerm
  rw [pow_mul]
  positivity
theorem coshTaylorTerm_abs (x : ℝ) (k : ℕ) :
    coshTaylorTerm |x| k = coshTaylorTerm x k := by
  simp only [coshTaylorTerm, pow_mul, sq_abs]
theorem summable_coshTaylorTerm (x : ℝ) : Summable (coshTaylorTerm x) := by
  unfold coshTaylorTerm
  exact (Real.hasSum_cosh x).summable
theorem summable_coshTaylorTail (J : ℕ) (x : ℝ) :
    Summable (fun k => coshTaylorTerm x (k + (J + 1))) :=
  (summable_nat_add_iff (J + 1)).mpr (summable_coshTaylorTerm x)
theorem coshTaylorRemainder_eq_tsum (J : ℕ) (x : ℝ) :
    coshTaylorRemainder J x =
      ∑' k : ℕ, coshTaylorTerm x (k + (J + 1)) := by
  have h := (summable_coshTaylorTerm x).sum_add_tsum_nat_add (J + 1)
  have he : (∑' k : ℕ, coshTaylorTerm x k) = Real.cosh x := by
    simpa only [coshTaylorTerm] using (Real.hasSum_cosh x).tsum_eq
  rw [he] at h
  change coshTaylorHead J x +
    (∑' k : ℕ, coshTaylorTerm x (k + (J + 1))) = Real.cosh x at h
  unfold coshTaylorRemainder
  linarith
theorem coshTaylorRemainder_nonneg (J : ℕ) (x : ℝ) :
    0 ≤ coshTaylorRemainder J x := by
  rw [coshTaylorRemainder_eq_tsum]
  exact tsum_nonneg (fun k => coshTaylorTerm_nonneg x _)
theorem coshTaylorRemainder_abs (J : ℕ) (x : ℝ) :
    coshTaylorRemainder J |x| = coshTaylorRemainder J x := by
  simp only [coshTaylorRemainder, coshTaylorHead, Real.cosh_abs,
    coshTaylorTerm_abs]
theorem coshTaylorRemainder_zero (J : ℕ) :
    coshTaylorRemainder J 0 = 0 := by
  rw [coshTaylorRemainder_eq_tsum]
  have hz (k : ℕ) : coshTaylorTerm 0 (k + (J + 1)) = 0 := by
    have hn : 2 * (k + (J + 1)) ≠ 0 := by omega
    simp [coshTaylorTerm, zero_pow hn]
  simp_rw [hz]
  simp
theorem coshTaylorRemainder_le_cosh_sub_one (J : ℕ) (x : ℝ) :
    coshTaylorRemainder J x ≤ Real.cosh x - 1 := by
  have hh : 1 ≤ coshTaylorHead J x := by
    have h := Finset.single_le_sum (s := Finset.range (J + 1))
      (f := coshTaylorTerm x)
      (fun i hi => coshTaylorTerm_nonneg x i)
      (by simp : 0 ∈ Finset.range (J + 1))
    simpa [coshTaylorHead, coshTaylorTerm] using h
  unfold coshTaylorRemainder
  linarith
private theorem unit_pow_le_one (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ n : ℕ, q ^ n ≤ 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      q ^ n * q ≤ 1 * q := mul_le_mul_of_nonneg_right ih hq0
      _ ≤ 1 := by simpa using hq1
theorem coshTaylorRemainder_mul_le (J : ℕ) (q x : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    coshTaylorRemainder J (q * x) ≤
      q ^ (2 * (J + 1)) * coshTaylorRemainder J x := by
  have hb (k : ℕ) :
      coshTaylorTerm (q * x) (k + (J + 1)) ≤
        q ^ (2 * (J + 1)) * coshTaylorTerm x (k + (J + 1)) := by
    have hp : q ^ (2 * (k + (J + 1))) ≤ q ^ (2 * (J + 1)) := by
      rw [show 2 * (k + (J + 1)) = 2 * (J + 1) + 2 * k by omega, pow_add]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (unit_pow_le_one q hq0 hq1 (2 * k))
          (pow_nonneg hq0 (2 * (J + 1)))
    have he : coshTaylorTerm (q * x) (k + (J + 1)) =
        q ^ (2 * (k + (J + 1))) * coshTaylorTerm x (k + (J + 1)) := by
      simp only [coshTaylorTerm, mul_pow]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hp (coshTaylorTerm_nonneg x _)
  calc
    _ = ∑' k : ℕ, coshTaylorTerm (q * x) (k + (J + 1)) :=
      coshTaylorRemainder_eq_tsum J (q * x)
    _ ≤ ∑' k : ℕ, q ^ (2 * (J + 1)) * coshTaylorTerm x (k + (J + 1)) :=
      Summable.tsum_le_tsum hb (summable_coshTaylorTail J (q * x))
        ((summable_coshTaylorTail J x).mul_left _)
    _ = q ^ (2 * (J + 1)) * coshTaylorRemainder J x := by
      rw [tsum_mul_left, ← coshTaylorRemainder_eq_tsum]
theorem coshTaylorRemainder_frequency_le (J : ℕ) (u v t : ℝ)
    (hv : 0 < v) (hu : |u| ≤ v) (ht : 0 ≤ t) :
    coshTaylorRemainder J (u * t) ≤
      (|u| / v) ^ (2 * (J + 1)) * (Real.cosh (v * t) - 1) := by
  have hq0 : 0 ≤ |u| / v := div_nonneg (abs_nonneg u) hv.le
  have hq1 : |u| / v ≤ 1 := (div_le_one hv).mpr hu
  have he : coshTaylorRemainder J (u * t) =
      coshTaylorRemainder J ((|u| / v) * (v * t)) := by
    calc
      _ = coshTaylorRemainder J |u * t| :=
        (coshTaylorRemainder_abs J (u * t)).symm
      _ = coshTaylorRemainder J (|u| * t) := by rw [abs_mul, abs_of_nonneg ht]
      _ = _ := by congr 1; field_simp [ne_of_gt hv]
  rw [he]
  exact (coshTaylorRemainder_mul_le J (|u| / v) (v * t) hq0 hq1).trans
    (mul_le_mul_of_nonneg_left (coshTaylorRemainder_le_cosh_sub_one J (v * t))
      (pow_nonneg hq0 _))

theorem coshTaylorHead_succ (J : ℕ) (x : ℝ) :
    coshTaylorHead (J + 1) x = coshTaylorHead J x + coshTaylorTerm x (J + 1) := by
  unfold coshTaylorHead
  rw [Finset.sum_range_succ]
theorem coshTaylorRemainder_eq_term_add (J : ℕ) (x : ℝ) :
    coshTaylorRemainder J x =
      coshTaylorTerm x (J + 1) + coshTaylorRemainder (J + 1) x := by
  unfold coshTaylorRemainder
  rw [coshTaylorHead_succ]
  ring
theorem coshTaylorTerm_succ_le_cosh_sub_one (j : ℕ) (x : ℝ) :
    coshTaylorTerm x (j + 1) ≤ Real.cosh x - 1 := by
  have he := coshTaylorRemainder_eq_term_add j x
  have hn := coshTaylorRemainder_nonneg (j + 1) x
  have hb := coshTaylorRemainder_le_cosh_sub_one j x
  linarith
theorem coshTaylorHead_eq_one_add (J : ℕ) (x : ℝ) :
    coshTaylorHead J x =
      1 + ∑ k ∈ Finset.range J, coshTaylorTerm x (k + 1) := by
  induction J with
  | zero => simp [coshTaylorHead, coshTaylorTerm]
  | succ J ih =>
    rw [coshTaylorHead_succ, ih, Finset.sum_range_succ]
    ring
theorem cosh_eq_one_add_head_add_remainder (J : ℕ) (x : ℝ) :
    Real.cosh x = 1 +
      (∑ k ∈ Finset.range J, coshTaylorTerm x (k + 1)) +
      coshTaylorRemainder J x := by
  rw [coshTaylorRemainder, coshTaylorHead_eq_one_add]
  ring
theorem coshTaylorHead_one (x : ℝ) :
    coshTaylorHead 1 x = 1 + x ^ 2 / 2 := by
  norm_num [coshTaylorHead, coshTaylorTerm, Finset.sum_range_succ]
theorem coshTaylorRemainder_one (x : ℝ) :
    coshTaylorRemainder 1 x = Real.cosh x - 1 - x ^ 2 / 2 := by
  rw [coshTaylorRemainder, coshTaylorHead_one]
  ring

end Real
