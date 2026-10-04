import RiemannResearch.Analysis.MarkedFourierTail
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual tent Fourier integral

The literal compactly supported function `max (v - |x|) 0` is connected to
the previously proved closed-form inverse-square Fourier bound. Both interval
endpoint terms are kept in the affine-exponential primitive.
-/

noncomputable section
open MeasureTheory Complex
open scoped FourierTransform

namespace RiemannResearch.Analysis.TentFourierIntegral

/-- Exact affine-exponential integral, including both boundary values. -/
theorem integral_affine_mul_cexp (A B c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    (∫ x in a..b, (A + B * (x : ℂ)) * Complex.exp (c * (x : ℂ))) =
      ((A + B * (b : ℂ)) / c - B / c ^ 2) * Complex.exp (c * (b : ℂ)) -
      ((A + B * (a : ℂ)) / c - B / c ^ 2) * Complex.exp (c * (a : ℂ)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hid := hasDerivAt_id (x : ℂ)
    have haff := ((hid.const_mul B).const_add A).div_const c
    have hexp := (hid.const_mul c).cexp
    have hd := (haff.sub_const (B / c ^ 2)).mul hexp
    simp only [mul_one] at hd
    have he : B / c * Complex.exp (c * (x : ℂ)) +
        ((A + B * (x : ℂ)) / c - B / c ^ 2) *
          (Complex.exp (c * (x : ℂ)) * c) =
        (A + B * (x : ℂ)) * Complex.exp (c * (x : ℂ)) := by
      field_simp [hc]
      ring
    exact (hd.congr_deriv he).comp_ofReal
  · apply Continuous.intervalIntegrable
    fun_prop

/-- The two genuine half-interval tent integrals. -/
def splitTentIntegral (v : ℝ) (c : ℂ) : ℂ :=
  (∫ x in (-v)..0, ((v : ℂ) + (x : ℂ)) * Complex.exp (c * (x : ℂ))) +
  (∫ x in 0..v, ((v : ℂ) - (x : ℂ)) * Complex.exp (c * (x : ℂ)))

theorem splitTentIntegral_of_ne_zero (v : ℝ) (c : ℂ) (hc : c ≠ 0) :
    splitTentIntegral v c =
      (Complex.exp (c * (v : ℂ)) + Complex.exp (-(c * (v : ℂ))) - 2) / c ^ 2 := by
  unfold splitTentIntegral
  have hl := integral_affine_mul_cexp (v : ℂ) 1 c hc (-v) 0
  have hr := integral_affine_mul_cexp (v : ℂ) (-1) c hc 0 v
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hl hr
  rw [hl, hr]
  simp only [Complex.ofReal_zero, Complex.ofReal_neg, mul_zero,
    Complex.exp_zero, mul_one, zero_add, add_zero]
  rw [show c * -(v : ℂ) = -(c * (v : ℂ)) by ring]
  field_simp [hc]
  ring

theorem splitTentIntegral_zero (v : ℝ) : splitTentIntegral v 0 = (v ^ 2 : ℝ) := by
  unfold splitTentIntegral
  simp only [zero_mul, Complex.exp_zero, mul_one]
  have hi (a b : ℝ) : (∫ x in a..b, (x : ℂ)) = ((b ^ 2 - a ^ 2) / 2 : ℝ) := by
    rw [intervalIntegral.integral_ofReal, integral_id]
  have hcont : Continuous (fun x : ℝ => (x : ℂ)) := by fun_prop
  rw [intervalIntegral.integral_add
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (v : ℂ)) volume (-v) 0)
      (hcont.intervalIntegrable (-v) 0),
    intervalIntegral.integral_sub
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (v : ℂ)) volume 0 v)
      (hcont.intervalIntegrable 0 v),
    intervalIntegral.integral_const, intervalIntegral.integral_const, hi, hi]
  simp only [Complex.real_smul, Complex.ofReal_zero, zero_sub, sub_zero,
    Complex.ofReal_neg, neg_sq]
  push_cast
  ring

/-- The compactly supported real tent, including the two zero endpoints. -/
def tent (v x : ℝ) : ℝ := max (v - |x|) 0

theorem tent_continuous (v : ℝ) : Continuous (tent v) := by
  unfold tent
  fun_prop

theorem tent_eq_zero_of_le_abs {v x : ℝ} (hx : v ≤ |x|) : tent v x = 0 := by
  unfold tent
  exact max_eq_right (sub_nonpos.mpr hx)

theorem tent_support_subset (v : ℝ) : Function.support (tent v) ⊆ Set.Ioc (-v) v := by
  intro x hx
  have hpos : 0 < v - |x| := by
    have hn : max (v - |x|) 0 ≠ 0 := hx
    by_contra h
    exact hn (max_eq_right (le_of_not_gt h))
  constructor <;> linarith [neg_abs_le x, le_abs_self x]

theorem tent_integrable (v : ℝ) : Integrable (tent v) :=
  (tent_continuous v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (Set.Subset.trans (tent_support_subset v) Set.Ioc_subset_Icc_self))

/-- Fourier integrand of the actual real tent. -/
def tentIntegrand (v : ℝ) (c : ℂ) (x : ℝ) : ℂ :=
  (tent v x : ℂ) * Complex.exp (c * (x : ℂ))

theorem tentIntegrand_continuous (v : ℝ) (c : ℂ) :
    Continuous (tentIntegrand v c) := by
  unfold tentIntegrand tent
  fun_prop

theorem tentIntegrand_support_subset (v : ℝ) (c : ℂ) :
    Function.support (tentIntegrand v c) ⊆ Set.Ioc (-v) v := by
  intro x hx
  apply tent_support_subset v
  intro hz
  apply hx
  simp [tentIntegrand, hz]

theorem tentIntegrand_integrable (v : ℝ) (c : ℂ) : Integrable (tentIntegrand v c) :=
  (tentIntegrand_continuous v c).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (Set.Subset.trans (tentIntegrand_support_subset v c) Set.Ioc_subset_Icc_self))

theorem integral_tentIntegrand_eq_split (v : ℝ) (hv : 0 ≤ v) (c : ℂ) :
    (∫ x, tentIntegrand v c x) = splitTentIntegral v c := by
  rw [← intervalIntegral.integral_eq_integral_of_support_subset
    (tentIntegrand_support_subset v c)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((tentIntegrand_continuous v c).intervalIntegrable (-v) 0)
    ((tentIntegrand_continuous v c).intervalIntegrable 0 v)]
  unfold splitTentIntegral
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -v ≤ (0 : ℝ))] at hx
    have ha : |x| = -x := abs_of_nonpos hx.2
    have hp : 0 ≤ v + x := by linarith [hx.1]
    simp only [tentIntegrand, tent, ha, sub_neg_eq_add, max_eq_left hp,
      Complex.ofReal_add]
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hv] at hx
    have ha : |x| = x := abs_of_nonneg hx.1
    have hp : 0 ≤ v - x := by linarith [hx.2]
    simp only [tentIntegrand, tent, ha, max_eq_left hp, Complex.ofReal_sub]

/-- Exact Fourier normalization, with frequency `α` in cycles per unit. -/
theorem fourier_tent_eq_split (v : ℝ) (hv : 0 ≤ v) (α : ℝ) :
    𝓕 (fun x : ℝ => (tent v x : ℂ)) α =
      splitTentIntegral v ((-2 * Real.pi * α : ℝ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ x, tentIntegrand v ((-2 * Real.pi * α : ℝ) * I) x := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      unfold tentIntegrand
      simp only [smul_eq_mul]
      have he : Complex.exp (((-2 * Real.pi * α : ℝ) : ℂ) * I * (x : ℂ)) =
          Complex.exp (((-2 * Real.pi * x * α : ℝ) : ℂ) * I) := by
        congr 1
        push_cast
        ring
      rw [he]
      ring
    _ = _ := integral_tentIntegrand_eq_split v hv _

/-- The actual Fourier transform is the exact sinc-square formula used in
`MarkedFourierTail`; zero frequency is handled separately and exactly. -/
theorem fourier_tent_eq_tentTransform (v : ℝ) (hv : 0 ≤ v) (α : ℝ) :
    𝓕 (fun x : ℝ => (tent v x : ℂ)) α =
      (MarkedFourierTail.tentTransform v α : ℂ) := by
  rw [fourier_tent_eq_split v hv α]
  by_cases hα : α = 0
  · subst α
    simp [MarkedFourierTail.tentTransform, splitTentIntegral_zero]
  · have hr : -2 * Real.pi * α ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hα
    have hc : (((-2 * Real.pi * α : ℝ) : ℂ) * I) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) Complex.I_ne_zero
    rw [splitTentIntegral_of_ne_zero v _ hc]
    have hp : (((-2 * Real.pi * α : ℝ) : ℂ) * I) * (v : ℂ) =
        -((2 * Real.pi * v * α : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [hp]
    have hnp : -(-((2 * Real.pi * v * α : ℝ) : ℂ) * I) =
        ((2 * Real.pi * v * α : ℝ) : ℂ) * I := by ring
    rw [hnp]
    have he := Complex.two_cos ((2 * Real.pi * v * α : ℝ) : ℂ)
    rw [add_comm] at he
    rw [← he, ← Complex.ofReal_cos]
    have hd : (((( -2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2) =
        -4 * ((Real.pi * α : ℝ) : ℂ) ^ 2 := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hd]
    have hs := congrArg Complex.ofReal (Real.sin_sq_eq_half_sub (Real.pi * v * α))
    rw [show 2 * (Real.pi * v * α) = 2 * Real.pi * v * α by ring] at hs
    push_cast at hs
    rw [MarkedFourierTail.tentTransform, if_neg hα, div_pow]
    push_cast
    have hpa : (((Real.pi * α : ℝ) : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hα)
    rw [hs]
    field_simp [hpa, Complex.ofReal_ne_zero.mpr hα,
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring

theorem fourier_tent_norm_le_inverse_square (v : ℝ) (hv : 0 ≤ v)
    (α : ℝ) (hα : α ≠ 0) :
    ‖𝓕 (fun x : ℝ => (tent v x : ℂ)) α‖ ≤ 1 / (Real.pi ^ 2 * α ^ 2) := by
  have hn : 0 ≤ MarkedFourierTail.tentTransform v α := by
    unfold MarkedFourierTail.tentTransform
    split <;> positivity
  rw [fourier_tent_eq_tentTransform v hv α, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hn]
  exact MarkedFourierTail.tentTransform_le_inverse_square v hα

end RiemannResearch.Analysis.TentFourierIntegral
