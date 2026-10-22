import RiemannResearch.RH.AnnularPrimePairTargets
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Unconditional rational negativity of the annular model coefficient

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The exponential estimates use finite Taylor certificates from Mathlib;
no floating-point evaluation, local axiom, or arithmetic hypothesis is used.
The actual Euler constant and pi are Mathlib's constants.

Pinned Mathlib source reviewed: 51e6992efd06126df61a496bebf8f49482a4e129.
The strengthened bound is -51611/1536000, compared with the paper's
-15883/614400. The prime-pair model asymptotic itself remains separate.
-/

set_option autoImplicit false
noncomputable section

namespace RiemannResearch.RH.AnnularPrimePair

theorem log_two_lt_seven_tenths : Real.log 2 < (7 / 10 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
  have hs := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 7 / 10) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  linarith

theorem log_three_lt_eleven_tenths : Real.log 3 < (11 / 10 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).2
  have hs := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 11 / 10) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  linarith

theorem exp_ninety_seven_hundredths_lt :
    Real.exp (97 / 100 : ℝ) < (66 / 25 : ℝ) := by
  have hb := Real.exp_bound' (x := (97 / 100 : ℝ)) (n := 4)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  linarith

theorem ninety_seven_fiftieths_lt_log_seven :
    (97 / 50 : ℝ) < Real.log 7 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 7)).2
  have hu := exp_ninety_seven_hundredths_lt
  have hp := (mul_self_lt_mul_self_iff
    (Real.exp_nonneg (97 / 100 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 66 / 25)).mp hu
  rw [show (97 / 50 : ℝ) = 97 / 100 + 97 / 100 by norm_num,
    Real.exp_add]
  nlinarith

theorem exp_nine_tenths_lt_five_halves :
    Real.exp (9 / 10 : ℝ) < (5 / 2 : ℝ) := by
  have hb := Real.exp_bound' (x := (9 / 10 : ℝ)) (n := 4)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  linarith

theorem nine_fifths_lt_log_two_pi :
    (9 / 5 : ℝ) < Real.log (2 * Real.pi) := by
  apply (Real.lt_log_iff_exp_lt (by linarith [Real.pi_pos] :
    (0 : ℝ) < 2 * Real.pi)).2
  have hu := exp_nine_tenths_lt_five_halves
  have hp := (mul_self_lt_mul_self_iff
    (Real.exp_nonneg (9 / 10 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 5 / 2)).mp hu
  rw [show (9 / 5 : ℝ) = 9 / 10 + 9 / 10 by norm_num, Real.exp_add]
  nlinarith [Real.pi_gt_d2]

/-- A strictly stronger bound than the paper's elementary certificate.
It is unconditional, using actual Mathlib logarithms, pi, and Euler constant. -/
theorem ModelCoefficient_lt_stronger_rational :
    ModelCoefficient < -(51611 / 1536000 : ℝ) := by
  have h2 := log_two_lt_seven_tenths
  have h3 := log_three_lt_eleven_tenths
  have h7 := ninety_seven_fiftieths_lt_log_seven
  have hpi := nine_fifths_lt_log_two_pi
  have hgamma := Real.one_half_lt_eulerMascheroniConstant
  unfold ModelCoefficient
  nlinarith

/-- The paper's certificate no longer has explicit logarithm hypotheses. -/
theorem ModelCoefficient_lt_rational :
    ModelCoefficient < -(15883 / 614400 : ℝ) :=
  ModelCoefficient_lt_stronger_rational.trans (by norm_num)

theorem ModelCoefficient_lt_neg_one_thirty_second :
    ModelCoefficient < -(1 / 32 : ℝ) :=
  ModelCoefficient_lt_stronger_rational.trans (by norm_num)

theorem ModelCoefficient_neg : ModelCoefficient < 0 :=
  ModelCoefficient_lt_stronger_rational.trans (by norm_num)

end RiemannResearch.RH.AnnularPrimePair
