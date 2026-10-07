import RiemannResearch.RH.DigammaBernoulliCells
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic

/-!
# Arbitrary-order Bernoulli-cell expansion for actual digamma

The analytic input is the proved actual cell-error series for `Complex.digamma`.
The cell expansion is derived from concrete Bernoulli integration by parts.
No Binet or digamma asymptotic formula is an assumption.

The exact cell remainder is used in the actual infinite digamma expansion.

Source for the classical asymptotic statement: NIST DLMF 5.11.2
(https://dlmf.nist.gov/5.11.E2). The formal proof uses the actual digamma
partial-fraction series and Bernoulli integration by parts.
-/

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped BigOperators Topology

namespace RiemannResearch.RH.DigammaBernoulliRemainder

open RiemannResearch.RH.DigammaAsymptotic
open RiemannResearch.RH.DigammaBernoulliCells

/-- The initial cell is the actual negative first Bernoulli integral. -/
theorem cellError_eq_neg_bernoulliCell_one {x : ℝ} (hx : 0 < x) :
    cellError x = -bernoulliCell 1 x := by
  have huderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (bernoulliFun 1) (1 : ℝ) u := by
    intro u _
    simpa using hasDerivAt_bernoulliFun 1 u
  have hvderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => (x + v)⁻¹) (-((x + u)⁻¹) ^ 2) u := by
    intro u hu
    have huIcc : u ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hxu : x + u ≠ 0 := ne_of_gt (by linarith [huIcc.1])
    simpa only [neg_div, one_div, inv_pow, id_eq] using
      ((hasDerivAt_id u).const_add x).fun_inv hxu
  have hvint : IntervalIntegrable
      (fun u : ℝ => -((x + u)⁻¹) ^ 2) volume 0 1 :=
    ((continuousOn_inverse_shift hx).pow 2).neg.intervalIntegrable
  have hinvint : IntervalIntegrable
      (fun u : ℝ => (x + u)⁻¹) volume 0 1 :=
    (continuousOn_inverse_shift hx).intervalIntegrable
  have hlogderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => Real.log (x + v)) ((x + u)⁻¹) u := by
    intro u hu
    have huIcc : u ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hxu : x + u ≠ 0 := ne_of_gt (by linarith [huIcc.1])
    simpa only [one_div, one_mul, id_eq] using
      ((hasDerivAt_id u).const_add x).log hxu
  have hlog : (∫ u in (0 : ℝ)..1, (x + u)⁻¹) =
      Real.log (x + 1) - Real.log x := by
    simpa only [add_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hlogderiv hinvint
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul huderiv hvderiv
    (intervalIntegrable_const) hvint
  have hfun : (fun u : ℝ => bernoulliFun 1 u * (-((x + u)⁻¹) ^ 2)) =
      (fun u : ℝ => -(bernoulliFun 1 u * ((x + u)⁻¹) ^ 2)) := by
    funext u
    ring
  rw [hfun, intervalIntegral.integral_neg] at hparts
  simp only [one_mul] at hparts
  rw [hlog] at hparts
  change -bernoulliCell 1 x =
    bernoulliFun 1 1 * (x + 1)⁻¹ - bernoulliFun 1 0 * (x + 0)⁻¹ -
      (Real.log (x + 1) - Real.log x) at hparts
  simp only [bernoulliFun_one, add_zero] at hparts
  dsimp [cellError]
  linarith

/-- Exact expansion to any consecutive inverse-power order, with the actual
Bernoulli cell remainder retained before estimates. -/
theorem cellError_expansion {x : ℝ} (hx : 0 < x) (m : ℕ) :
    cellError x =
      (∑ j ∈ Finset.range m,
        bernoulliCoefficient (j + 2) * inversePowerDifference x (j + 2)) -
          bernoulliCell (m + 1) x := by
  induction m with
  | zero => simpa using cellError_eq_neg_bernoulliCell_one hx
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hrec := bernoulliCell_recurrence hx (m + 1) (by omega)
      linarith

end RiemannResearch.RH.DigammaBernoulliRemainder
