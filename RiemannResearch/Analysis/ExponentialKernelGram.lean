/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exponential kernel Gram integral

For positive rate, the Volterra feature has an integrable pair product whose
integral is exp (-rate * |x-y|)/(2*rate). Finite sums therefore have a square
integral Gram formula and are nonnegative, without any condition on the points
or coefficients. This is finite-configuration positivity, not yet the analogous
quadratic form for an arbitrary L2 function.

Source: user-provided RH_Local_to_Global_Trace_Attack_Plan_2026-09-05,
Section on exponential Gram factorization, supplies the integral representation.
RH consumer: ScrewArchimedeanPositivity.
-/

namespace RiemannResearch.Analysis
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def exponentialVolterraFeature (α x z : ℝ) : ℝ :=
  (Iic x).indicator (fun z => Real.exp (-α*(x-z))) z

theorem exponentialVolterraFeature_mul (α x y z : ℝ) :
    exponentialVolterraFeature α x z * exponentialVolterraFeature α y z =
      (Iic (min x y)).indicator
        (fun z => Real.exp (-α*(x+y))*Real.exp ((2*α)*z)) z := by
  by_cases hx : z ≤ x <;> by_cases hy : z ≤ y
  · simp only [exponentialVolterraFeature, Set.mem_Iic, Set.indicator_apply,
      hx, hy, le_min hx hy, ↓reduceIte]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · simp [exponentialVolterraFeature, hx, hy]
  · simp [exponentialVolterraFeature, hx, hy]
  · simp [exponentialVolterraFeature, hx, hy]

theorem integrable_exponentialVolterraFeature_mul {α : ℝ} (hα : 0 < α) (x y : ℝ) :
    Integrable (fun z => exponentialVolterraFeature α x z * exponentialVolterraFeature α y z) := by
  simp_rw [exponentialVolterraFeature_mul]
  have hi : IntegrableOn (fun z => Real.exp (-α*(x+y))*Real.exp ((2*α)*z))
      (Iic (min x y)) := (integrableOn_exp_mul_Iic (by positivity : 0 < 2*α)
        (min x y)).const_mul (Real.exp (-α*(x+y)))
  exact hi.integrable_indicator measurableSet_Iic

theorem integral_exponentialVolterraFeature_mul {α : ℝ} (hα : 0 < α) (x y : ℝ) :
    (∫ z, exponentialVolterraFeature α x z * exponentialVolterraFeature α y z) =
      Real.exp (-α*|x-y|)/(2*α) := by
  simp_rw [exponentialVolterraFeature_mul]
  rw [integral_indicator measurableSet_Iic, integral_const_mul,
    integral_exp_mul_Iic (by positivity : 0 < 2*α), ← mul_div_assoc, ← Real.exp_add]
  have he : -α*(x+y) + 2*α*min x y = -α*|x-y| := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  rw [he]

theorem exponentialKernel_finite_gram {ι : Type*} [Fintype ι]
    {α : ℝ} (hα : 0 < α) (x c : ι → ℝ) :
    (∑ i, ∑ j, c i * Real.exp (-α*|x i-x j|) * c j) =
      2*α * (∫ z, (∑ i, c i * exponentialVolterraFeature α (x i) z)^2) := by
  have he (z : ℝ) : (∑ i, c i * exponentialVolterraFeature α (x i) z)^2 =
      ∑ i, ∑ j, c i * (exponentialVolterraFeature α (x i) z *
        exponentialVolterraFeature α (x j) z) * c j := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hij (i j : ι) : Integrable (fun z => c i *
      (exponentialVolterraFeature α (x i) z * exponentialVolterraFeature α (x j) z) * c j) :=
    ((integrable_exponentialVolterraFeature_mul hα (x i) (x j)).const_mul (c i)).mul_const (c j)
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hij i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hij _ j),
    integral_mul_const, integral_const_mul, integral_exponentialVolterraFeature_mul hα]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  field_simp

theorem exponentialKernel_finite_nonneg {ι : Type*} [Fintype ι]
    {α : ℝ} (hα : 0 < α) (x c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * Real.exp (-α*|x i-x j|) * c j := by
  rw [exponentialKernel_finite_gram hα]
  exact mul_nonneg (by positivity) (integral_nonneg (fun z => sq_nonneg _))

end
end RiemannResearch.Analysis
