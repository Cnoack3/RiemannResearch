import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nonvanishing annular Mellin multipliers

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

Source: the user's October 9 centered-arithmetic report, Sections 15 and 18.
The nonvanishing argument is extended to every dilation base b > 1 and every
nonnegative real shift, on the whole right half-plane. It is algebra and
complex exponential analysis. ActualAnnularMellin supplies the Mellin identity
of the actual prime signal on Re(s)>1. Identification with the weight integral
and its entire removable extension are separate analytic obligations.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.AnnularMellin

def dilationFactor (b a : ℝ) (z : ℂ) : ℂ :=
  1 - Complex.exp (-(z + (a : ℂ)) * (Real.log b : ℂ))

theorem norm_dilation_exponential_lt_one {b a : ℝ} {z : ℂ}
    (hb : 1 < b) (ha : 0 ≤ a) (hz : 0 < z.re) :
    ‖Complex.exp (-(z + (a : ℂ)) * (Real.log b : ℂ))‖ < 1 := by
  have hl : 0 < Real.log b := Real.log_pos hb
  have he :
      (-(z + (a : ℂ)) * (Real.log b : ℂ)).re =
        -(z.re + a) * Real.log b := by
    simp [Complex.mul_re]
  rw [Complex.norm_exp, he]
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_neg_of_pos (by linarith) hl

/-- Exact norm of the exponential used by the annular factor. -/
theorem norm_dilation_exponential (b a : ℝ) (z : ℂ) :
    ‖Complex.exp (-(z + (a : ℂ)) * (Real.log b : ℂ))‖ =
      Real.exp (-(z.re + a) * Real.log b) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- Two-sided control retains the full complex phase. It is valid without
any half-plane assumption; the lower bound becomes positive there. -/
theorem dilationFactor_norm_bounds (b a : ℝ) (z : ℂ) :
    1 - Real.exp (-(z.re + a) * Real.log b) ≤ ‖dilationFactor b a z‖ ∧
      ‖dilationFactor b a z‖ ≤ 1 + Real.exp (-(z.re + a) * Real.log b) := by
  have hl := norm_sub_norm_le (1 : ℂ)
    (Complex.exp (-(z + (a : ℂ)) * (Real.log b : ℂ)))
  have hu := norm_sub_le (1 : ℂ)
    (Complex.exp (-(z + (a : ℂ)) * (Real.log b : ℂ)))
  rw [norm_one, norm_dilation_exponential] at hl hu
  exact ⟨hl, hu⟩

/-- Uniform control on every fixed positive half-plane. -/
theorem dilationFactor_uniform_norm_bounds {b a δ : ℝ} {z : ℂ}
    (hb : 1 < b) (hz : δ ≤ z.re) :
    1 - Real.exp (-(δ + a) * Real.log b) ≤ ‖dilationFactor b a z‖ ∧
      ‖dilationFactor b a z‖ ≤ 1 + Real.exp (-(δ + a) * Real.log b) := by
  have hlog : 0 < Real.log b := Real.log_pos hb
  have he : Real.exp (-(z.re + a) * Real.log b) ≤
      Real.exp (-(δ + a) * Real.log b) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hz hlog.le
    nlinarith
  obtain ⟨hl, hu⟩ := dilationFactor_norm_bounds b a z
  constructor <;> linarith

/-- The uniform lower bound is strictly positive. -/
theorem dilationFactor_uniform_lower_pos {b a δ : ℝ}
    (hb : 1 < b) (ha : 0 ≤ a) (hδ : 0 < δ) :
    0 < 1 - Real.exp (-(δ + a) * Real.log b) := by
  have he : Real.exp (-(δ + a) * Real.log b) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos hb)
  linarith

theorem dilationFactor_ne_zero {b a : ℝ} {z : ℂ}
    (hb : 1 < b) (ha : 0 ≤ a) (hz : 0 < z.re) :
    dilationFactor b a z ≠ 0 := by
  unfold dilationFactor
  apply sub_ne_zero.mpr
  intro he
  have hn := norm_dilation_exponential_lt_one hb ha hz
  have hnorm :
      ‖Complex.exp (-(z + (a : ℂ)) * (Real.log b : ℂ))‖ = 1 := by
    rw [← he]
    norm_num
  linarith

theorem dilationFactor_analyticAt (b a : ℝ) (z : ℂ) :
    AnalyticAt ℂ (dilationFactor b a) z := by
  exact analyticAt_const.sub
    (((analyticAt_id.add analyticAt_const).neg.mul analyticAt_const).cexp)

/-- Every finite family of nonnegative shifts preserves every point with
positive real part; no restriction to a critical-strip zero is needed. -/
theorem finite_dilation_product_ne_zero {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) {b : ℝ} {z : ℂ}
    (hb : 1 < b) (ha : ∀ i ∈ s, 0 ≤ a i) (hz : 0 < z.re) :
    (∏ i ∈ s, dilationFactor b (a i) z) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact dilationFactor_ne_zero hb (ha i hi) hz

def secondRieszDenominator (z : ℂ) : ℂ := z * (z + 1) * (z + 2)

theorem nonneg_shift_ne_zero {z : ℂ} {a : ℝ}
    (hz : 0 < z.re) (ha : 0 ≤ a) :
    z + (a : ℂ) ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
  linarith

theorem secondRieszDenominator_ne_zero {z : ℂ} (hz : 0 < z.re) :
    secondRieszDenominator z ≠ 0 := by
  have h0 : z ≠ 0 := by
    intro he
    simp [he] at hz
  have h1 : z + 1 ≠ 0 := by
    simpa using nonneg_shift_ne_zero hz (by norm_num : (0 : ℝ) ≤ 1)
  have h2 : z + 2 ≠ 0 := by
    simpa using nonneg_shift_ne_zero hz (by norm_num : (0 : ℝ) ≤ 2)
  exact mul_ne_zero (mul_ne_zero h0 h1) h2

def multiplier (z : ℂ) : ℂ :=
  2 * dilationFactor 2 0 z * dilationFactor 2 1 z *
    dilationFactor 2 2 z / secondRieszDenominator z

theorem multiplier_norm (z : ℂ) :
    ‖multiplier z‖ =
      (2 * ‖dilationFactor 2 0 z‖ * ‖dilationFactor 2 1 z‖ *
        ‖dilationFactor 2 2 z‖) / ‖secondRieszDenominator z‖ := by
  unfold multiplier
  rw [Complex.norm_div, Complex.norm_mul, Complex.norm_mul, Complex.norm_mul]
  norm_num

private theorem three_factor_le {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    a₀ * a₁ * a₂ ≤ b₀ * b₁ * b₂ := by
  have hb₀ : 0 ≤ b₀ := ha₀.trans h₀
  have hb₁ : 0 ≤ b₁ := ha₁.trans h₁
  exact mul_le_mul (mul_le_mul h₀ h₁ ha₁ hb₀) h₂ ha₂
    (mul_nonneg hb₀ hb₁)

/-- Two-sided full-multiplier bounds at every positive real part. The
oscillatory annular factors are bounded rather than replaced by a limit. -/
theorem multiplier_norm_bounds {z : ℂ} (hz : 0 < z.re) :
    (2 * (1 - Real.exp (-z.re * Real.log 2)) *
      (1 - Real.exp (-(z.re + 1) * Real.log 2)) *
      (1 - Real.exp (-(z.re + 2) * Real.log 2))) /
        ‖secondRieszDenominator z‖ ≤ ‖multiplier z‖ ∧
    ‖multiplier z‖ ≤
      (2 * (1 + Real.exp (-z.re * Real.log 2)) *
      (1 + Real.exp (-(z.re + 1) * Real.log 2)) *
      (1 + Real.exp (-(z.re + 2) * Real.log 2))) /
        ‖secondRieszDenominator z‖ := by
  have h₀ := dilationFactor_norm_bounds 2 0 z
  have h₁ := dilationFactor_norm_bounds 2 1 z
  have h₂ := dilationFactor_norm_bounds 2 2 z
  have hp₀ : 0 < 1 - Real.exp (-z.re * Real.log 2) := by
    simpa using dilationFactor_uniform_lower_pos (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) ≤ 0) hz
  have hp₁ := dilationFactor_uniform_lower_pos (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) ≤ 1) hz
  have hp₂ := dilationFactor_uniform_lower_pos (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) ≤ 2) hz
  simp only [add_zero] at h₀
  have hl := three_factor_le hp₀.le hp₁.le hp₂.le h₀.1 h₁.1 h₂.1
  have hu := three_factor_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    h₀.2 h₁.2 h₂.2
  have hl₂ := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 2)
  have hu₂ := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2)
  rw [multiplier_norm]
  constructor
  · apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    nlinarith
  · apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    nlinarith

theorem multiplier_ne_zero {z : ℂ} (hz : 0 < z.re) :
    multiplier z ≠ 0 := by
  unfold multiplier
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (dilationFactor_ne_zero (by norm_num) (by norm_num) hz))
        (dilationFactor_ne_zero (by norm_num) (by norm_num) hz))
      (dilationFactor_ne_zero (by norm_num) (by norm_num) hz)
  · exact secondRieszDenominator_ne_zero hz

theorem multiplier_analyticAt {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ multiplier z := by
  exact (((analyticAt_const.mul (dilationFactor_analyticAt 2 0 z)).mul
    (dilationFactor_analyticAt 2 1 z)).mul
    (dilationFactor_analyticAt 2 2 z)).div
    ((analyticAt_id.mul (analyticAt_id.add analyticAt_const)).mul
      (analyticAt_id.add analyticAt_const))
    (secondRieszDenominator_ne_zero hz)

/-- A multiplier changes a zero coefficient but cannot annihilate it. This
statement concerns the exact coefficient; it does not assert an explicit formula. -/
theorem full_zero_coefficient_ne_zero {z : ℂ} {m : ℕ}
    (hz : 0 < z.re) (hm : 0 < m) :
    -(m : ℂ) * multiplier z ≠ 0 := by
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))
  · exact multiplier_ne_zero hz

end RiemannResearch.Analysis.AnnularMellin
