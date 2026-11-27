import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A Gaussian upper bound for the reduced sine pair density

The proof uses the global cubic lower bound for sine and the exact second
Gaussian moment. The proposed estimate comes from the user-provided argument.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis.GaussianGapTests

/-- Global quadratic repulsion bound in the radian argument. -/
theorem one_sub_sinc_sq_le (y : ℝ) : 1 - Real.sinc y ^ 2 ≤ y ^ 2 / 3 := by
  have hpos (x : ℝ) (hx : 0 < x) : 1 - x ^ 2 / 6 ≤ Real.sinc x := by
    rw [Real.sinc_of_ne_zero hx.ne', le_div_iff₀ hx]
    nlinarith only [Real.sin_ge_sub_cube hx.le]
  have h : 1 - y ^ 2 / 6 ≤ Real.sinc y := by
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · simpa only [neg_sq, Real.sinc_neg] using hpos (-y) (neg_pos.mpr hy)
    · simp
    · exact hpos y hy
  nlinarith only [h, sq_nonneg (1 - Real.sinc y)]

/-- Exact unnormalized Gaussian second moment on the real line. -/
theorem integral_gaussian_second_moment {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, x ^ 2 * Real.exp (-a * x ^ 2)) =
      Real.sqrt Real.pi / (2 * a ^ (3 / 2 : ℝ)) := by
  let f := fun x : ℝ => x ^ 2 * Real.exp (-a * x ^ 2)
  have hi : Integrable f := by
    simpa only [f, Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq ha (by norm_num : (-1 : ℝ) < (2 : ℕ))
  have he : (∫ x in Iic 0, f x) = ∫ x in Ioi 0, f x := by
    simpa [f] using (integral_comp_neg_Ioi 0 f).symm
  have hg : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    ring
  have hh := integral_rpow_mul_exp_neg_mul_rpow
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (-1 : ℝ) < 2) ha
  rw [show -((2 : ℝ) + 1) / 2 = -(3 / 2) by norm_num,
    show ((2 : ℝ) + 1) / 2 = 3 / 2 by norm_num, Real.rpow_neg ha.le, hg] at hh
  change (∫ x, f x) = _
  rw [← integral_add_compl measurableSet_Ioi hi, compl_Ioi, he]
  have hh' : (∫ x in Ioi 0, f x) =
      (a ^ (3 / 2 : ℝ))⁻¹ * (1 / 2) * (Real.sqrt Real.pi / 2) := by
    simpa only [f, Real.rpow_two] using hh
  rw [hh']
  ring

/-- The full signed-displacement integral for the sine model at any positive precision. -/
theorem sine_gaussian_moment_le {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, Real.exp (-a * x ^ 2) * (1 - Real.sinc (Real.pi * x) ^ 2)) ≤
      Real.pi ^ (5 / 2 : ℝ) / (6 * a ^ (3 / 2 : ℝ)) := by
  let K := fun x : ℝ => 1 - Real.sinc (Real.pi * x) ^ 2
  have hk (x : ℝ) : 0 ≤ K x := by
    have h := Real.abs_sinc_le_one (Real.pi * x)
    nlinarith only [sq_abs (Real.sinc (Real.pi * x)),
      (sq_le_sq₀ (abs_nonneg (Real.sinc (Real.pi * x))) zero_le_one).2 h]
  have hk' : Continuous K :=
    continuous_const.sub ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2)
  have hi : Integrable (fun x : ℝ => Real.exp (-a * x ^ 2) * K x) := by
    apply (integrable_exp_neg_mul_sq ha).mono' (by fun_prop (disch := positivity))
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hk x))]
      exact mul_le_of_le_one_right (Real.exp_nonneg _) (sub_le_self _ (sq_nonneg _))
  have h2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-a * x ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq ha (by norm_num : (-1 : ℝ) < (2 : ℕ))
  have hp : Real.pi ^ (5 / 2 : ℝ) = Real.pi ^ 2 * Real.sqrt Real.pi := by
    rw [show (5 / 2 : ℝ) = (2 : ℕ) + (1 / 2 : ℝ) by norm_num,
      Real.rpow_add Real.pi_pos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  calc
    _ ≤ ∫ x : ℝ, (Real.pi ^ 2 / 3) * (x ^ 2 * Real.exp (-a * x ^ 2)) := by
      apply integral_mono hi (h2.const_mul _)
      intro x
      calc
        _ ≤ Real.exp (-a * x ^ 2) * ((Real.pi * x) ^ 2 / 3) :=
          mul_le_mul_of_nonneg_left (one_sub_sinc_sq_le _) (Real.exp_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul, integral_gaussian_second_moment ha, hp]; ring

/--
info: 'RiemannResearch.Analysis.GaussianGapTests.sine_gaussian_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sine_gaussian_moment_le

end RiemannResearch.Analysis.GaussianGapTests
