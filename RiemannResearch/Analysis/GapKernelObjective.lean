/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A rational lower certificate for Lamzouri's small-gap functional

For the Gaussian polynomial test choose a positive rational radius r so
that the square of its scaled endpoint is exactly r². An upper bound on
exp(-r²) then follows by reciprocating a positive finite Taylor sum.
Lamzouri, *The distribution of small gaps between zeros of the Riemann
zeta function*, Theorem 3.3, equation (3.12), defines the functional.
<https://arxiv.org/html/2611.14486v1#S3.E12>
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.Analysis.GapKernelObjective

/-- Normalized polynomial times the scaled Gaussian, at rational radius r. -/
def test (r θ q : ℝ) (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  r / (θ * Real.sqrt Real.pi * q) * Real.exp (-((r / θ) * x)^2) *
    P (((r / θ) * x)^2)

/-- Exact integration via the polynomial primitive H satisfying H-H' = P. -/
theorem functional_eq {r θ q : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hq : 0 < q)
    {P H : ℝ → ℝ} (hP : Continuous P) (hH : ∀ y, HasDerivAt H (H y - P y) y) :
    test r θ q P 0 + 2 * (∫ x in (0 : ℝ)..θ, x * test r θ q P x) =
      ((r / θ) * P 0 + (θ / r) * (H 0 - Real.exp (-(r ^ 2)) * H (r ^ 2))) /
        (Real.sqrt Real.pi * q) := by
  let b := r / θ
  let F := fun x : ℝ => -Real.exp (-(b*x)^2) * H ((b*x)^2)
  let f := fun x : ℝ => (2*b^2*x) * Real.exp (-(b*x)^2) * P ((b*x)^2)
  have hderiv (x : ℝ) : HasDerivAt F (f x) x := by
    have hg := ((hasDerivAt_id x).const_mul b).pow 2
    have hd := (hg.neg.exp.neg).mul ((hH _).comp x hg)
    change HasDerivAt (fun y : ℝ => -Real.exp (-(b*y)^2) * H ((b*y)^2)) _ x at hd
    change HasDerivAt (fun y : ℝ => -Real.exp (-(b*y)^2) * H ((b*y)^2)) (f x) x
    convert hd using 1
    all_goals try rfl
    all_goals try dsimp [f, Function.comp_def]
    all_goals try ring
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (hf.intervalIntegrable 0 θ)
  have hb : b ≠ 0 := (div_pos hr hθ).ne'
  have hroot := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have he (x : ℝ) : x * test r θ q P x =
      ((θ / r) / (2 * Real.sqrt Real.pi * q)) * f x := by
    dsimp [test, f, b]
    field_simp [hr.ne', hθ.ne', hq.ne', hroot]
    <;> ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, hi]
  dsimp [F, test]
  rw [show b*θ = r by dsimp [b]; field_simp]
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), neg_zero, Real.exp_zero]
  field_simp [hr.ne', hθ.ne', hq.ne', hroot]
  <;> ring

/-- Rational Taylor lower sum of exp(z). -/
def expLower (z : ℚ) (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, z^i / (i.factorial : ℚ)

theorem exp_neg_le_inv_lower {z : ℚ} (hz : 0 ≤ z) {n : ℕ}
    (hs : 0 < expLower z n) : Real.exp (-(z : ℝ)) ≤ 1 / (expLower z n : ℝ) := by
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by exact_mod_cast hs)
  have h := Real.sum_le_exp_of_nonneg (x := (z : ℝ)) (by exact_mod_cast hz) n
  simpa [expLower, Rat.cast_sum, Rat.cast_div, Rat.cast_pow] using h

/-- Verify the scalar functional using only rational comparisons besides
Mathlib's exponential and pi theorems. -/
theorem objective_gt_one {r θ p h₀ h₁ q : ℚ} {n : ℕ}
    (hr : 0 < r) (hθ : 0 < θ) (hq : 0 < q) (hh : 0 ≤ h₁)
    (hs : 0 < expLower (r ^ 2) n)
    (hcert : (177245385090551603 / 100000000000000000 : ℚ) * q <
      (r / θ) * p + (θ / r) * (h₀ - h₁ / expLower (r ^ 2) n)) :
    (1 : ℝ) < (((r : ℝ) / θ)*p + ((θ : ℝ)/r) *
      ((h₀ : ℝ) - Real.exp (-((r : ℝ)^2)) * h₁)) / (Real.sqrt Real.pi * q) := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hp : Real.sqrt Real.pi < (177245385090551603 / 100000000000000000 : ℝ) := by
    nlinarith only [Real.sq_sqrt Real.pi_pos.le, Real.pi_lt_d20, Real.sqrt_nonneg Real.pi]
  apply (lt_div_iff₀ (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) hq')).mpr
  rw [one_mul]
  have hc : (177245385090551603/100000000000000000 : ℝ) * q <
      ((r : ℝ)/θ)*p + ((θ : ℝ)/r)*((h₀ : ℝ) - h₁/(expLower (r ^ 2) n : ℝ)) := by
    have Hreal : (((177245385090551603/100000000000000000 : ℚ) * q : ℚ) : ℝ) <
        (((r/θ)*p + (θ/r)*(h₀-h₁/expLower (r ^ 2) n) : ℚ) : ℝ) := by exact_mod_cast hcert
    push_cast at Hreal
    exact Hreal
  apply ((mul_lt_mul_of_pos_right hp hq').trans hc).trans_le
  have hth : 0 ≤ (θ : ℝ) / r := div_nonneg (by exact_mod_cast hθ.le) (by exact_mod_cast hr.le)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hth
  apply sub_le_sub le_rfl
  have H := mul_le_mul_of_nonneg_right (exp_neg_le_inv_lower (sq_nonneg r) hs)
    (show 0 ≤ (h₁ : ℝ) by exact_mod_cast hh)
  simpa only [Rat.cast_pow, one_div, div_eq_mul_inv, one_mul, mul_comm] using H

end RiemannResearch.Analysis.GapKernelObjective
