/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
/-!
# Exact finite twisted second moments

The finite expansion retains every signed off-diagonal term. Continuity
on the compact integration interval is the only analytic input.

Source: the finite expansion proposed in the user-provided
Conrey_Baluyot_Right_Boundary_Continuation_2026-11-15.md.
This is elementary finite-sum algebra and integration, not an asymptotic
twisted-zeta moment estimate.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
namespace Complex
def finiteTwistedMoment (f : ℝ → ℂ) (u v q : ℝ) : ℂ :=
  ∫ t in u..v, (‖f t‖ ^ 2 : ℝ) * exp (I * t * q)
theorem finiteTwistedMoment_zero (f : ℝ → ℂ) (u v : ℝ) :
    finiteTwistedMoment f u v 0 = ((∫ t in u..v, ‖f t‖ ^ 2 : ℝ) : ℂ) := by
  simp only [finiteTwistedMoment, Complex.ofReal_zero, mul_zero, exp_zero, mul_one]
  exact intervalIntegral.integral_ofReal
theorem exp_phase_mul_star (p q t : ℝ) :
    exp (I * t * p) * star (exp (I * t * q)) = exp (I * t * (p-q)) := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp
  ring
private theorem ofReal_norm_sq_mul (z : ℂ) : (‖z‖ ^ 2 : ℝ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
theorem finite_sum_norm_sq_expansion {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (z : ℂ) (t : ℝ) :
    (‖z * ∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2 : ℝ) =
    ∑ m ∈ S, ∑ n ∈ S, a m * star (a n) *
      ((‖z‖ ^ 2 : ℝ) * exp (I * t * (ω m - ω n))) := by
  rw [norm_mul, mul_pow, Complex.ofReal_mul, ofReal_norm_sq_mul
    (∑ n ∈ S, a n * exp (I * t * ω n))]
  simp only [star_sum, star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = (a m * star (a n)) * ((‖z‖ ^ 2 : ℝ) *
      (exp (I*t*ω m) * star (exp (I*t*ω n)))) := by ring
    _ = _ := by rw [exp_phase_mul_star]
theorem integral_finite_sum_norm_sq {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (f : ℝ → ℂ) (u v : ℝ)
    (hf : ContinuousOn f (uIcc u v)) :
    ((∫ t in u..v, ‖f t * ∑ n ∈ S, a n * exp (I * t * ω n)‖ ^ 2 : ℝ) : ℂ) =
    ∑ m ∈ S, ∑ n ∈ S, a m * star (a n) * finiteTwistedMoment f u v (ω m - ω n) := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [finite_sum_norm_sq_expansion]
  have hc (m n : ι) : ContinuousOn (fun t : ℝ =>
      a m * star (a n) * ((‖f t‖ ^ 2 : ℝ) * exp (I * t * (ω m - ω n)))) (uIcc u v) := by
    exact continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn
      (hf.norm.pow 2)).mul (by fun_prop))
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      unfold finiteTwistedMoment
      rw [intervalIntegral.integral_const_mul]
      simp only [Complex.ofReal_sub]
    · intro n hn
      exact (hc m n).intervalIntegrable
  · intro m hm
    exact (continuousOn_finsetSum S (fun n _ => hc m n)).intervalIntegrable


def finiteTwistedOffDiagonal {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (f : ℝ → ℂ) (u v : ℝ) : ℂ :=
  ∑ m ∈ S, ∑ n ∈ S, if m = n then 0 else
    a m * star (a n) * finiteTwistedMoment f u v (ω m - ω n)

theorem integral_finite_sum_norm_sq_diagonal {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℂ) (ω : ι → ℝ) (f : ℝ → ℂ) (u v : ℝ)
    (hf : ContinuousOn f (uIcc u v)) :
    ((∫ t in u..v, ‖f t * ∑ n ∈ S, a n * exp (I*t*ω n)‖ ^ 2 : ℝ) : ℂ) =
    (((∑ n ∈ S, ‖a n‖ ^ 2) * (∫ t in u..v, ‖f t‖ ^ 2) : ℝ) : ℂ) +
      finiteTwistedOffDiagonal S a ω f u v := by
  rw [integral_finite_sum_norm_sq S a ω f u v hf]
  unfold finiteTwistedOffDiagonal
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hsplit : (∑ n ∈ S, a m * star (a n) * finiteTwistedMoment f u v (ω m - ω n)) =
      (∑ n ∈ S, if m = n then
        a m * star (a n) * finiteTwistedMoment f u v (ω m - ω n) else 0) +
      ∑ n ∈ S, if m = n then 0 else
        a m * star (a n) * finiteTwistedMoment f u v (ω m - ω n) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp
  rw [hsplit]
  simp only [Finset.sum_ite_eq, hm, if_true, sub_self,
    finiteTwistedMoment_zero, ← ofReal_norm_sq_mul]
  push_cast
  rfl
end Complex
