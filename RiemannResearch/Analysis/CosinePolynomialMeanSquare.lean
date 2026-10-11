import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Exact signed mean square of a finite cosine polynomial

Source: the on-paper prime-polynomial continuation of 11 October 2026.
This module isolates the finite trigonometric and integration identity. It
does not assert the prime number theorem, an asymptotic mean-value estimate,
an approximation to actual zero counts, or a pair-correlation theorem.

The difference-frequency diagonal and every sum-frequency term are retained.
The main identity also holds at `T = 0` with Lean's field convention; the
normalization of the zero-frequency kernel requires `0 < T`.

-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.CosinePolynomialMeanSquare

variable {ι : Type*}

/-- A finite real cosine polynomial with a common translation of the argument. -/
def cosinePolynomial (s : Finset ι) (a w : ι → ℝ) (b t : ℝ) : ℝ :=
  ∑ i ∈ s, a i * Real.cos ((t + b) * w i)

/-- The normalized finite-window cosine kernel, with no frequency omitted. -/
def cosineWindow (T b v : ℝ) : ℝ :=
  (1 / T) * ∫ t in (0 : ℝ)..T, Real.cos ((t + b) * v)

theorem cosineTerm_intervalIntegrable (T b v : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.cos ((t + b) * v)) volume 0 T := by
  exact (show Continuous (fun t : ℝ => Real.cos ((t + b) * v)) by
    fun_prop).intervalIntegrable 0 T

theorem cosinePolynomial_continuous
    (s : Finset ι) (a w : ι → ℝ) (b : ℝ) :
    Continuous (cosinePolynomial s a w b) := by
  classical
  unfold cosinePolynomial
  fun_prop

theorem cosinePolynomial_sq_intervalIntegrable
    (s : Finset ι) (a w : ι → ℝ) (T b : ℝ) :
    IntervalIntegrable (fun t => cosinePolynomial s a w b t ^ 2) volume 0 T := by
  exact ((cosinePolynomial_continuous s a w b).pow 2).intervalIntegrable 0 T

/-- Product-to-sum with the difference and sum frequencies both present. -/
theorem cosine_product_to_sum (x y : ℝ) :
    Real.cos x * Real.cos y =
      (Real.cos (x - y) + Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- Exact finite expansion before any integration or absolute-value bound. -/
theorem cosinePolynomial_sq
    (s : Finset ι) (a w : ι → ℝ) (b t : ℝ) :
    cosinePolynomial s a w b t ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (a i * a j / 2) *
        (Real.cos ((t + b) * (w i - w j)) +
          Real.cos ((t + b) * (w i + w j))) := by
  classical
  unfold cosinePolynomial
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_sub, mul_add, Real.cos_sub, Real.cos_add]
  ring

/-- Exact normalized mean square, retaining the full signed double sum. -/
theorem cosinePolynomial_meanSquare
    (s : Finset ι) (a w : ι → ℝ) (T b : ℝ) :
    (1 / T) * (∫ t in (0 : ℝ)..T, cosinePolynomial s a w b t ^ 2) =
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, a i * a j *
        (cosineWindow T b (w i - w j) +
          cosineWindow T b (w i + w j)) := by
  classical
  let f : ι → ι → ℝ → ℝ := fun i j t => (a i * a j / 2) *
    (Real.cos ((t + b) * (w i - w j)) +
      Real.cos ((t + b) * (w i + w j)))
  have hf (i j : ι) : Continuous (f i j) := by
    dsimp [f]
    fun_prop
  have hrow (i : ι) :
      IntervalIntegrable (fun t => ∑ j ∈ s, f i j t) volume 0 T := by
    exact (show Continuous (fun t => ∑ j ∈ s, f i j t) by
      dsimp [f]
      fun_prop).intervalIntegrable 0 T
  have hfun : (fun t => cosinePolynomial s a w b t ^ 2) =
      (fun t => ∑ i ∈ s, ∑ j ∈ s, f i j t) := by
    funext t
    exact cosinePolynomial_sq s a w b t
  calc
    (1 / T) * (∫ t in (0 : ℝ)..T, cosinePolynomial s a w b t ^ 2) =
        (1 / T) * ∑ i ∈ s, ∑ j ∈ s, ∫ t in (0 : ℝ)..T, f i j t := by
      rw [hfun]
      congr 1
      rw [intervalIntegral.integral_finsetSum (fun i hi => hrow i)]
      apply Finset.sum_congr rfl
      intro i hi
      exact intervalIntegral.integral_finsetSum
        (fun j hj => (hf i j).intervalIntegrable 0 T)
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (1 / T) * (∫ t in (0 : ℝ)..T, f i j t) := by
      simp only [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, (a i * a j / 2) *
        (cosineWindow T b (w i - w j) +
          cosineWindow T b (w i + w j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          (cosineTerm_intervalIntegrable T b (w i - w j))
          (cosineTerm_intervalIntegrable T b (w i + w j))]
      unfold cosineWindow
      ring
    _ = (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, a i * a j *
        (cosineWindow T b (w i - w j) +
          cosineWindow T b (w i + w j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

@[simp] theorem cosineWindow_zero (T b : ℝ) (hT : 0 < T) :
    cosineWindow T b 0 = 1 := by
  simp [cosineWindow, ne_of_gt hT]

theorem cosineWindow_neg (T b v : ℝ) :
    cosineWindow T b (-v) = cosineWindow T b v := by
  simp [cosineWindow, mul_neg, Real.cos_neg]

end RiemannResearch.Analysis.CosinePolynomialMeanSquare
