import RiemannResearch.RH.DigammaAsymptotic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Actual Bernoulli-cell integration by parts

This is a concrete cell-level development. It uses the actual Bernoulli
polynomial functions, their proved derivatives, and their endpoint values.
No Binet formula or digamma asymptotic is assumed.

The cell identities support the all-order positive-real digamma expansion.

Source for the classical asymptotic statement: NIST DLMF 5.11.2
(https://dlmf.nist.gov/5.11.E2). The formal proof uses the actual digamma
partial-fraction series and Bernoulli integration by parts.
-/

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped BigOperators Topology

namespace RiemannResearch.RH.DigammaBernoulliCells

open RiemannResearch.RH.DigammaAsymptotic

/-- The actual Bernoulli-polynomial cell integral. -/
def bernoulliCell (k : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, bernoulliFun k u * ((x + u)⁻¹) ^ (k + 1)

/-- The coefficient of the inverse-power endpoint difference. -/
def bernoulliCoefficient (k : ℕ) : ℝ := (bernoulli k : ℝ) / (k : ℝ)

theorem hasDerivAt_inverse_shift_power (x u : ℝ)
    (hxu : x + u ≠ 0) (k : ℕ) :
    HasDerivAt (fun v : ℝ => ((x + v)⁻¹) ^ k)
      (-(k : ℝ) * ((x + u)⁻¹) ^ (k + 1)) u := by
  induction k with
  | zero => simpa using (hasDerivAt_const u (1 : ℝ))
  | succ k ih =>
      have hbase := ((hasDerivAt_id u).const_add x).fun_inv hxu
      have h := ih.fun_mul hbase
      convert h using 1 <;> first
        | rfl
        | (funext v; simpa only [id_eq] using pow_succ ((x + v)⁻¹) k)
        | (simp only [Nat.cast_add, Nat.cast_one, pow_succ, id_eq];
            field_simp [hxu] <;> ring)

theorem continuousOn_inverse_shift {x : ℝ} (hx : 0 < x) :
    ContinuousOn (fun u : ℝ => (x + u)⁻¹) (uIcc (0 : ℝ) 1) := by
  apply (continuous_const.add continuous_id).continuousOn.inv₀
  intro u hu
  have huIcc : u ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
  have hu0 : 0 ≤ u := huIcc.1
  exact ne_of_gt (by linarith : 0 < x + u)

private theorem inverse_shift_power_intervalIntegrable {x : ℝ} (hx : 0 < x)
    (k : ℕ) :
    IntervalIntegrable (fun u : ℝ => ((x + u)⁻¹) ^ k) volume 0 1 :=
  ((continuousOn_inverse_shift hx).pow k).intervalIntegrable

/-- Exact recurrence obtained by integrating the actual Bernoulli derivative.
The endpoint coefficient contains the literal Bernoulli number. -/
theorem bernoulliCell_recurrence {x : ℝ} (hx : 0 < x)
    (k : ℕ) (hk : 1 ≤ k) :
    bernoulliCell k x =
      -bernoulliCoefficient (k + 1) * inversePowerDifference x (k + 1) +
        bernoulliCell (k + 1) x := by
  have hn : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have huderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => bernoulliFun (k + 1) v / ((k + 1 : ℕ) : ℝ))
        (bernoulliFun k u) u := by
    intro u _
    simpa only [Nat.cast_add, Nat.cast_one] using antideriv_bernoulliFun k u
  have hvderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => ((x + v)⁻¹) ^ (k + 1))
        (-((k + 1 : ℕ) : ℝ) * ((x + u)⁻¹) ^ ((k + 1) + 1)) u := by
    intro u hu
    have huIcc : u ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hu0 : 0 ≤ u := huIcc.1
    exact hasDerivAt_inverse_shift_power x u (ne_of_gt (by linarith)) (k + 1)
  have hvint : IntervalIntegrable
      (fun u : ℝ => -((k + 1 : ℕ) : ℝ) *
        ((x + u)⁻¹) ^ ((k + 1) + 1)) volume 0 1 :=
    (((continuousOn_inverse_shift hx).pow ((k + 1) + 1)).const_mul
      (-((k + 1 : ℕ) : ℝ))).intervalIntegrable
  have hparts := integral_mul_deriv_eq_deriv_mul huderiv hvderiv
    (intervalIntegrable_bernoulliFun k 0 1) hvint
  have hfun :
      (fun u : ℝ => (bernoulliFun (k + 1) u / ((k + 1 : ℕ) : ℝ)) *
        (-((k + 1 : ℕ) : ℝ) * ((x + u)⁻¹) ^ ((k + 1) + 1))) =
      (fun u : ℝ => -(bernoulliFun (k + 1) u *
        ((x + u)⁻¹) ^ ((k + 1) + 1))) := by
    funext u
    field_simp [hn]
    <;> ring
  rw [hfun, intervalIntegral.integral_neg] at hparts
  rw [bernoulliFun_endpoints_eq_of_ne_one (by omega : k + 1 ≠ 1),
    bernoulliFun_eval_zero] at hparts
  simp only [add_zero] at hparts
  change -bernoulliCell (k + 1) x =
    bernoulliCoefficient (k + 1) * ((x + 1)⁻¹) ^ (k + 1) -
      bernoulliCoefficient (k + 1) * x⁻¹ ^ (k + 1) -
        bernoulliCell k x at hparts
  dsimp [inversePowerDifference]
  nlinarith [hparts]

theorem intervalIntegrable_inversePower_kernel {x : ℝ} (hx : 0 < x) (k : ℕ) :
    IntervalIntegrable (fun u : ℝ => ((x + u)⁻¹) ^ (k + 1)) volume 0 1 :=
  ((continuousOn_inverse_shift hx).pow (k + 1)).intervalIntegrable

/-- Exact positive-cell inverse-power integral, in telescoping form. -/
theorem inversePower_kernel_integral {x : ℝ} (hx : 0 < x)
    (k : ℕ) (hk : 0 < k) :
    (∫ u in (0 : ℝ)..1, ((x + u)⁻¹) ^ (k + 1)) =
      inversePowerDifference x k / (k : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => (-1 / (k : ℝ)) * ((x + v)⁻¹) ^ k)
        (((x + u)⁻¹) ^ (k + 1)) u := by
    intro u hu
    have huIcc : u ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hu0 : 0 ≤ u := huIcc.1
    have hxu : x + u ≠ 0 := ne_of_gt (by linarith : 0 < x + u)
    have h := (hasDerivAt_inverse_shift_power x u hxu k).const_mul (-1 / (k : ℝ))
    convert h using 1 <;> first | rfl | (field_simp [hkR] <;> ring)
  have hint : IntervalIntegrable
      (fun u : ℝ => ((x + u)⁻¹) ^ (k + 1)) volume 0 1 :=
    intervalIntegrable_inversePower_kernel hx k
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    (∫ u in (0 : ℝ)..1, ((x + u)⁻¹) ^ (k + 1)) =
        (-1 / (k : ℝ)) * ((x + 1)⁻¹) ^ k -
          (-1 / (k : ℝ)) * (x⁻¹) ^ k := by
            simpa only [add_zero] using hftc
    _ = inversePowerDifference x k / (k : ℝ) := by
      dsimp [inversePowerDifference]
      ring


end RiemannResearch.RH.DigammaBernoulliCells
