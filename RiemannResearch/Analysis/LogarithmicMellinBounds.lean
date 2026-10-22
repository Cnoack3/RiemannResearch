import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact logarithmic moments and finite head estimates for the differentiated,
phase-centered compressed Mellin cells. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.Analysis

theorem exp_weighted_moment_integrable (j : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ j * Real.exp (-y)) (Ioi 0) := by
  simpa using (integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := (j : ℝ))
    (by have h := Nat.cast_nonneg (α := ℝ) j; linarith) (by norm_num))

theorem exp_weighted_moment_integral (j : ℕ) :
    (∫ y in Ioi (0 : ℝ), y ^ j * Real.exp (-y)) = (j.factorial : ℝ) := by
  have h := Real.Gamma_eq_integral (s := (j : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  simpa [mul_comm] using h.symm

private theorem shifted_square_exp_integrable (L : ℝ) :
    IntegrableOn (fun y : ℝ => (y + L) ^ 2 * Real.exp (-y)) (Ioi 0) := by
  have h := ((exp_weighted_moment_integrable 2).add
    ((exp_weighted_moment_integrable 1).const_mul (2 * L))).add
      ((exp_weighted_moment_integrable 0).const_mul (L ^ 2))
  convert! h using 1
  funext y
  simp only [Pi.add_apply]
  ring

private theorem shifted_square_exp_integral (L : ℝ) :
    (∫ y in Ioi (0 : ℝ), (y + L) ^ 2 * Real.exp (-y)) = L ^ 2 + 2 * L + 2 := by
  have h₂ : IntegrableOn (fun y : ℝ => y ^ 2 * Real.exp (-y)) (Ioi 0) :=
    exp_weighted_moment_integrable 2
  have h₁ : IntegrableOn (fun y : ℝ => (2 * L) * (y ^ 1 * Real.exp (-y))) (Ioi 0) :=
    (exp_weighted_moment_integrable 1).const_mul (2 * L)
  have h₀ : IntegrableOn (fun y : ℝ => L ^ 2 * (y ^ 0 * Real.exp (-y))) (Ioi 0) :=
    (exp_weighted_moment_integrable 0).const_mul (L ^ 2)
  have h₂₁ : IntegrableOn (fun y : ℝ =>
      y ^ 2 * Real.exp (-y) + (2 * L) * (y ^ 1 * Real.exp (-y))) (Ioi 0) := h₂.add h₁
  calc
    _ = ∫ y in Ioi (0 : ℝ),
        (y ^ 2 * Real.exp (-y) + (2 * L) * (y ^ 1 * Real.exp (-y))) +
          L ^ 2 * (y ^ 0 * Real.exp (-y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      ring
    _ = _ := by
      rw [integral_add h₂₁ h₀, integral_add h₂ h₁,
        integral_const_mul, integral_const_mul,
        exp_weighted_moment_integral, exp_weighted_moment_integral,
        exp_weighted_moment_integral]
      norm_num
      ring

private theorem positive_exp_image {a : ℝ} (ha : 0 < a) :
    (fun y : ℝ => a * Real.exp y) '' Ioi (0 : ℝ) = Ioi a := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change a < a * Real.exp y
    have h := Real.one_lt_exp_iff.mpr (show 0 < y from hy)
    nlinarith
  · intro hx
    have hx' : a < x := hx
    have hx0 : 0 < x := ha.trans hx'
    refine ⟨Real.log (x / a), ?_, ?_⟩
    · change 0 < Real.log (x / a)
      exact Real.log_pos ((one_lt_div ha).mpr hx')
    · change a * Real.exp (Real.log (x / a)) = x
      rw [Real.exp_log (div_pos hx0 ha)]
      field_simp

private theorem positive_exp_injective {a : ℝ} (ha : 0 < a) :
    Set.InjOn (fun y : ℝ => a * Real.exp y) (Ioi 0) := by
  intro x hx y hy hxy
  exact Real.exp_injective (mul_left_cancel₀ (ne_of_gt ha) hxy)

private theorem positive_exp_deriv {a : ℝ} (ha : 0 < a) :
    ∀ y ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun y : ℝ => a * Real.exp y) (a * Real.exp y) (Ioi 0) y := by
  intro y hy
  exact ((Real.hasDerivAt_exp y).const_mul a).hasDerivWithinAt

private theorem logTail_change {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (fun y : ℝ => |a * Real.exp y| •
      (Real.log ((a * Real.exp y) / t) ^ 2 / (a * Real.exp y) ^ 2)) =
      (fun y : ℝ => (1 / a) * ((y + Real.log (a / t)) ^ 2 * Real.exp (-y))) := by
  funext y
  have hlog : Real.log ((a * Real.exp y) / t) = y + Real.log (a / t) := by
    rw [Real.log_div (mul_ne_zero (ne_of_gt ha) (Real.exp_ne_zero y)) (ne_of_gt ht),
      Real.log_mul (ne_of_gt ha) (Real.exp_ne_zero y), Real.log_exp,
      Real.log_div (ne_of_gt ha) (ne_of_gt ht)]
    ring
  rw [abs_of_pos (mul_pos ha (Real.exp_pos y)), smul_eq_mul, hlog, Real.exp_neg]
  field_simp

/-- Exact integrability of the centered logarithmic square on every positive tail. -/
theorem logTail_integrable (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => Real.log (x / t) ^ 2 / x ^ 2) (Ioi a) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (positive_exp_deriv ha) (positive_exp_injective ha)
    (fun x : ℝ => Real.log (x / t) ^ 2 / x ^ 2)
  rw [positive_exp_image ha, logTail_change ha ht] at h
  exact h.mpr ((shifted_square_exp_integrable (Real.log (a / t))).const_mul (1 / a))

/-- The complete centered derivative tail has this exact expression. -/
theorem logTail_integral (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    (∫ x in Ioi a, Real.log (x / t) ^ 2 / x ^ 2) =
      (Real.log (a / t) ^ 2 + 2 * Real.log (a / t) + 2) / a := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (positive_exp_deriv ha) (positive_exp_injective ha)
    (fun x : ℝ => Real.log (x / t) ^ 2 / x ^ 2)
  rw [positive_exp_image ha, logTail_change ha ht,
    integral_const_mul, shifted_square_exp_integral] at h
  simpa only [div_eq_mul_inv, mul_comm, mul_one, one_mul] using h

/-- A tail beginning between t/2 and t costs at most 4/t. -/
theorem logTail_le_four_div (a t : ℝ) (ht : 0 < t)
    (ha : t / 2 ≤ a) (hat : a ≤ t) :
    (∫ x in Ioi a, Real.log (x / t) ^ 2 / x ^ 2) ≤ 4 / t := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos ht) ha
  have hratio : (1 : ℝ) / 2 ≤ a / t := (le_div_iff₀ ht).mpr (by linarith)
  have hlogL : -1 ≤ Real.log (a / t) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hratio
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one] at h
    linarith
  have hlogU : Real.log (a / t) ≤ 0 :=
    Real.log_nonpos (div_nonneg ha0.le ht.le) ((div_le_one ht).mpr hat)
  have hpoly : Real.log (a / t) ^ 2 + 2 * Real.log (a / t) + 2 ≤ 2 := by
    have hp := mul_nonpos_of_nonpos_of_nonneg hlogU
      (show 0 ≤ Real.log (a / t) + 2 by linarith)
    nlinarith
  rw [logTail_integral a t ha0 ht]
  calc
    _ ≤ 2 / a := div_le_div_of_nonneg_right hpoly ha0.le
    _ ≤ 4 / t := by rw [div_le_div_iff₀ ha0 ht]; linarith

/-- At frequencies between one and two the entire centered derivative energy is ≤2. -/
theorem logTail_one_le_two (t : ℝ) (ht : 1 ≤ t) (ht2 : t ≤ 2) :
    (∫ x in Ioi (1 : ℝ), Real.log (x / t) ^ 2 / x ^ 2) ≤ 2 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [logTail_integral 1 t (by norm_num) ht0]
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlog1 : Real.log t ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos ht0
    linarith
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt ht0), Real.log_one]
  norm_num
  have hp := mul_nonpos_of_nonneg_of_nonpos hlog0
    (show Real.log t - 2 ≤ 0 by linarith)
  nlinarith

end RiemannResearch.Analysis
