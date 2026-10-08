import RiemannResearch.RH.ParetoStepIsometry
import RiemannResearch.RH.DigammaAsymptotic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Actual cell means and the complete raw fractional-part correction

The canonical weight is the physical Pareto mass. The mean and both squared
energies below are evaluated by actual interval integrals. Every variance and
cross term is retained before passing to complete summable series.

Source: Christian Noack, RH_CRT_Optimized_Gains_and_Uniform_Obstruction_20261007.md, correction-norm section. The cell formulas and strict variances are derived here from actual interval integrals.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.StepCorrectionNorm
open RiemannResearch.RH.Pareto

/-- Conditional mean of the raw fractional part in the positive cell `[n+1,n+2]`.
The density is `dx/x²`, not the uniform cell law. -/
def cellMean (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * ((n : ℝ) + 2) *
    (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) - ((n : ℝ) + 1)

/-- Actual raw fractional-part squared energy of the positive cell. -/
def rawResidueCellEnergy (n : ℕ) : ℝ :=
  2 - 1 / ((n : ℝ) + 2) - 2 * ((n : ℝ) + 1) *
    (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1))

/-- The complete removed cell variance, without dropping its conditional mean. -/
def centeredEnergy (n : ℕ) : ℝ :=
  rawResidueCellEnergy n - positiveWeight (n + 1) * (cellMean n) ^ 2

private theorem positive_kernel_continuous {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ContinuousOn (fun x : ℝ => 1 / x ^ k) (Icc a (a + 1)) := by
  apply continuousOn_const.div (continuousOn_id.pow k)
  intro x hx
  exact pow_ne_zero k (ne_of_gt (ha.trans_le hx.1))

private theorem positive_kernel_integrable {a : ℝ} (ha : 0 < a) (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => 1 / x ^ k) volume a (a + 1) :=
  (positive_kernel_continuous ha k).intervalIntegrable_of_Icc (by linarith)

private theorem integral_inv_square {a : ℝ} (ha : 0 < a) :
    (∫ x in a..a + 1, 1 / x ^ 2) = 1 / a - 1 / (a + 1) := by
  have hz : (0 : ℝ) ∉ uIcc a (a + 1) := by
    rw [uIcc_of_le (by linarith)]
    intro hx
    linarith [hx.1]
  have h := integral_zpow (a := a) (b := a + 1) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hz⟩)
  have heq : (fun x : ℝ => 1 / x ^ 2) = (fun x : ℝ => x ^ (-2 : ℤ)) := by
    funext x
    simp
  rw [heq, h]
  norm_num
  ring

private theorem integral_cell_first_moment {a : ℝ} (ha : 0 < a) :
    (∫ x in a..a + 1, (x - a) / x ^ 2) =
      Real.log (a + 1) - Real.log a - 1 / (a + 1) := by
  have hi := positive_kernel_integrable ha 1
  have hs := positive_kernel_integrable ha 2
  have heq : (∫ x in a..a + 1, (x - a) / x ^ 2) =
      ∫ x in a..a + 1, 1 / x - a * (1 / x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    field_simp [hx0]
    <;> ring
  rw [heq, intervalIntegral.integral_sub (by simpa only [pow_one] using hi) (hs.const_mul a),
    intervalIntegral.integral_const_mul, integral_one_div_of_pos ha (by linarith),
    integral_inv_square ha, Real.log_div (ne_of_gt (by linarith)) (ne_of_gt ha)]
  field_simp [ne_of_gt ha, ne_of_gt (by linarith : 0 < a + 1)]
  <;> ring

private theorem integral_cell_second_moment {a : ℝ} (ha : 0 < a) :
    (∫ x in a..a + 1, (x - a) ^ 2 / x ^ 2) =
      2 - 1 / (a + 1) - 2 * a * (Real.log (a + 1) - Real.log a) := by
  have hi := positive_kernel_integrable ha 1
  have hs := positive_kernel_integrable ha 2
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a (a + 1) :=
    continuous_const.intervalIntegrable _ _
  have heq : (∫ x in a..a + 1, (x - a) ^ 2 / x ^ 2) =
      ∫ x in a..a + 1, (1 - 2 * a * (1 / x)) + a ^ 2 * (1 / x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    field_simp [hx0]
    <;> ring
  rw [heq, intervalIntegral.integral_add
    (hconst.sub (by simpa only [pow_one] using hi.const_mul (2 * a))) (hs.const_mul (a ^ 2)),
    intervalIntegral.integral_sub hconst (by simpa only [pow_one] using hi.const_mul (2 * a)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_one, integral_one_div_of_pos ha (by linarith), integral_inv_square ha,
    Real.log_div (ne_of_gt (by linarith)) (ne_of_gt ha)]
  field_simp [ne_of_gt ha, ne_of_gt (by linarith : 0 < a + 1)]
  <;> ring

theorem cell_mass_integral (n : ℕ) :
    (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), 1 / x ^ 2) =
      positiveWeight (n + 1) := by
  have h := integral_inv_square (by positivity : 0 < (n : ℝ) + 1)
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] at h
  rw [h]
  unfold positiveWeight
  push_cast
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  <;> ring

theorem cellMoment_integral (n : ℕ) :
    (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2),
      (x - ((n : ℝ) + 1)) / x ^ 2) = positiveWeight (n + 1) * cellMean n := by
  have h := integral_cell_first_moment (by positivity : 0 < (n : ℝ) + 1)
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] at h
  rw [h]
  unfold positiveWeight cellMean
  push_cast
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  <;> ring

theorem rawResidueCellEnergy_integral (n : ℕ) :
    (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2),
      (x - ((n : ℝ) + 1)) ^ 2 / x ^ 2) = rawResidueCellEnergy n := by
  have h := integral_cell_second_moment (by positivity : 0 < (n : ℝ) + 1)
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] at h
  exact h

theorem cellMean_nonneg (n : ℕ) : 0 ≤ cellMean n := by
  have hw : 0 < positiveWeight (n + 1) := by unfold positiveWeight; positivity
  have h := intervalIntegral.integral_nonneg (μ := volume)
    (f := fun x : ℝ => (x - ((n : ℝ) + 1)) / x ^ 2)
    (a := (n : ℝ) + 1) (b := (n : ℝ) + 2) (by linarith)
    (fun x hx => div_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg x))
  rw [cellMoment_integral] at h
  exact (mul_nonneg_iff_of_pos_left hw).mp h

theorem cellMean_le_one (n : ℕ) : cellMean n ≤ 1 := by
  have hw : 0 < positiveWeight (n + 1) := by unfold positiveWeight; positivity
  have hi : IntervalIntegrable
      (fun x : ℝ => (x - ((n : ℝ) + 1)) / x ^ 2) volume
      ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply (continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < (n : ℝ) + 1) hx.1))
  have hk := positive_kernel_integrable (by positivity : 0 < (n : ℝ) + 1) 2
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] at hk
  have h := intervalIntegral.integral_mono_on (by linarith) hi hk (fun x hx => by
    apply div_le_div_of_nonneg_right (by linarith [hx.2] : x - ((n : ℝ) + 1) ≤ 1)
    exact sq_nonneg x)
  rw [cellMoment_integral, cell_mass_integral] at h
  nlinarith

theorem rawResidueCellEnergy_nonneg (n : ℕ) : 0 ≤ rawResidueCellEnergy n := by
  rw [← rawResidueCellEnergy_integral]
  exact intervalIntegral.integral_nonneg_of_forall (by linarith)
    (fun x => div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem rawResidueCellEnergy_le_weight (n : ℕ) :
    rawResidueCellEnergy n ≤ positiveWeight (n + 1) := by
  have hi : IntervalIntegrable
      (fun x : ℝ => (x - ((n : ℝ) + 1)) ^ 2 / x ^ 2) volume
      ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply ((continuousOn_id.sub continuousOn_const).pow 2).div (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < (n : ℝ) + 1) hx.1))
  have hk := positive_kernel_integrable (by positivity : 0 < (n : ℝ) + 1) 2
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] at hk
  have h := intervalIntegral.integral_mono_on (by linarith) hi hk (fun x hx => by
    apply div_le_div_of_nonneg_right ?_ (sq_nonneg x)
    have hlo : 0 ≤ x - ((n : ℝ) + 1) := by linarith [hx.1]
    have hhi : x - ((n : ℝ) + 1) ≤ 1 := by linarith [hx.2]
    nlinarith)
  rw [rawResidueCellEnergy_integral, cell_mass_integral] at h
  exact h

theorem scaled_cell_error_energy (n : ℕ) (b a : ℝ) :
    (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2),
      (b - a * (x - ((n : ℝ) + 1))) ^ 2 / x ^ 2) =
      positiveWeight (n + 1) * (b - a * cellMean n) ^ 2 + a ^ 2 * centeredEnergy n := by
  have hkernel := positive_kernel_integrable (by positivity : 0 < (n : ℝ) + 1) 2
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] at hkernel
  have hfirst : IntervalIntegrable
      (fun x : ℝ => (x - ((n : ℝ) + 1)) / x ^ 2) volume
      ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply (continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < (n : ℝ) + 1) hx.1))
  have hsecond : IntervalIntegrable
      (fun x : ℝ => (x - ((n : ℝ) + 1)) ^ 2 / x ^ 2) volume
      ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply ((continuousOn_id.sub continuousOn_const).pow 2).div (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < (n : ℝ) + 1) hx.1))
  have heq : (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2),
      (b - a * (x - ((n : ℝ) + 1))) ^ 2 / x ^ 2) =
      ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2),
      (b ^ 2 * (1 / x ^ 2) - (2 * b * a) * ((x - ((n : ℝ) + 1)) / x ^ 2)) +
        a ^ 2 * ((x - ((n : ℝ) + 1)) ^ 2 / x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [heq, intervalIntegral.integral_add
    ((hkernel.const_mul _).sub (hfirst.const_mul _)) (hsecond.const_mul _),
    intervalIntegral.integral_sub (hkernel.const_mul _) (hfirst.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, cell_mass_integral, cellMoment_integral,
    rawResidueCellEnergy_integral]
  unfold centeredEnergy
  ring

theorem centeredEnergy_nonneg (n : ℕ) : 0 ≤ centeredEnergy n := by
  have h := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (f := fun x : ℝ => (cellMean n - (x - ((n : ℝ) + 1))) ^ 2 / x ^ 2)
    (by linarith) (fun x => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs := scaled_cell_error_energy n (cellMean n) 1
  norm_num only [one_mul] at hs
  rw [hs] at h
  simpa using h

theorem centeredEnergy_le_raw (n : ℕ) : centeredEnergy n ≤ rawResidueCellEnergy n := by
  unfold centeredEnergy
  exact sub_le_self _ (mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))

theorem rawResidueCellEnergy_summable : Summable rawResidueCellEnergy := by
  have hs : Summable (fun n : ℕ => positiveWeight (n + 1)) :=
    (summable_nat_add_iff 1).mpr positiveWeight_summable
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (rawResidueCellEnergy_nonneg n)]
  exact rawResidueCellEnergy_le_weight n

theorem centeredEnergy_summable : Summable centeredEnergy := by
  apply rawResidueCellEnergy_summable.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (centeredEnergy_nonneg n)]
  exact centeredEnergy_le_raw n


/-- The weighted conditional mean is below the midpoint by the exact
trapezoidal correction, with its complete sign retained. -/
theorem cellMean_eq_half_sub_trapezoid (n : ℕ) :
    cellMean n = 1 / 2 - ((n : ℝ) + 1) * ((n : ℝ) + 2) *
      DigammaAsymptotic.cellError ((n : ℝ) + 1) := by
  unfold cellMean DigammaAsymptotic.cellError
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  <;> ring

theorem cellMean_le_half (n : ℕ) : cellMean n ≤ 1 / 2 := by
  rw [cellMean_eq_half_sub_trapezoid]
  exact sub_le_self _ (mul_nonneg (by positivity)
    (DigammaAsymptotic.cellError_nonneg (by positivity)))

/-- The raw cell energy and the positive trapezoidal correction are exactly
the same physical contribution. -/
theorem rawResidueCellEnergy_eq_trapezoid (n : ℕ) :
    rawResidueCellEnergy n = 2 * ((n : ℝ) + 1) *
      DigammaAsymptotic.cellError ((n : ℝ) + 1) := by
  unfold rawResidueCellEnergy DigammaAsymptotic.cellError
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  <;> ring

/-- Cancellation gives an exact compact variance formula. It is a variance,
so positivity follows from its integral rather than from a detached estimate. -/
theorem centeredEnergy_eq_log_square (n : ℕ) :
    centeredEnergy n = 1 - ((n : ℝ) + 1) * ((n : ℝ) + 2) *
      (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) ^ 2 := by
  unfold centeredEnergy rawResidueCellEnergy cellMean positiveWeight
  push_cast
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  <;> ring

theorem rawResidueCellEnergy_pos (n : ℕ) : 0 < rawResidueCellEnergy n := by
  rw [← rawResidueCellEnergy_integral]
  have hi : IntervalIntegrable
      (fun x : ℝ => (x - ((n : ℝ) + 1)) ^ 2 / x ^ 2) volume
      ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply ((continuousOn_id.sub continuousOn_const).pow 2).div (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < (n : ℝ) + 1) hx.1))
  apply intervalIntegral.intervalIntegral_pos_of_pos_on hi ?_ (by linarith)
  intro x hx
  apply div_pos (sq_pos_of_pos (by linarith [hx.1]))
  exact sq_pos_of_pos (lt_trans (by positivity) hx.1)

theorem cellMean_lt_half (n : ℕ) : cellMean n < 1 / 2 := by
  have hq := rawResidueCellEnergy_pos n
  rw [rawResidueCellEnergy_eq_trapezoid] at hq
  have hτ : 0 < DigammaAsymptotic.cellError ((n : ℝ) + 1) :=
    (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * ((n : ℝ) + 1))).mp hq
  rw [cellMean_eq_half_sub_trapezoid]
  exact sub_lt_self _ (mul_pos (by positivity) hτ)

/-- The removed variance is genuinely positive on every full physical cell. -/
theorem centeredEnergy_pos (n : ℕ) : 0 < centeredEnergy n := by
  have heq := scaled_cell_error_energy n (cellMean n) 1
  simp only [one_mul, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero,
    one_pow, zero_add] at heq
  rw [← heq]
  apply intervalIntegral.integral_pos (by linarith)
  · apply ((continuousOn_const.sub
      (continuousOn_id.sub continuousOn_const)).pow 2).div (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < (n : ℝ) + 1) hx.1))
  · intro x hx
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · refine ⟨(n : ℝ) + 2, ⟨by linarith, le_rfl⟩, ?_⟩
    apply div_pos ?_ (by positivity)
    apply sq_pos_of_ne_zero
    have hc := cellMean_le_half n
    intro hz
    linarith

theorem centeredEnergy_zero : centeredEnergy 0 = 1 - 2 * (Real.log 2) ^ 2 := by
  rw [centeredEnergy_eq_log_square]
  norm_num


/-- Every conditional physical cell mean is strictly positive. -/
theorem cellMean_pos (n : ℕ) : 0 < cellMean n := by
  have hw : 0 < positiveWeight (n + 1) := by unfold positiveWeight; positivity
  have hm : 0 < ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2),
      (x - ((n : ℝ) + 1)) / x ^ 2 := by
    apply intervalIntegral.integral_pos (by linarith)
    · apply (continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2)
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < (n : ℝ) + 1) hx.1))
    · intro x hx
      exact div_nonneg (by linarith [hx.1]) (sq_nonneg _)
    · refine ⟨(n : ℝ) + 2, ⟨by linarith, le_rfl⟩, ?_⟩
      exact div_pos (by linarith) (by positivity)
  rw [cellMoment_integral] at hm
  exact (mul_pos_iff_of_pos_left hw).mp hm



/-- The literal raw physical cell lies strictly below one third of its mass.
This improves certified tails by a factor of three. -/
theorem rawResidueCellEnergy_lt_third_weight (n : ℕ) :
    rawResidueCellEnergy n < positiveWeight (n + 1) / 3 := by
  have hτ := (DigammaAsymptotic.cellError_bernoulli_bounds
    (by positivity : 0 < (n : ℝ) + 1)).2
  have hbound := mul_le_mul_of_nonneg_left hτ
    (by positivity : 0 ≤ 2 * ((n : ℝ) + 1))
  rw [← rawResidueCellEnergy_eq_trapezoid] at hbound
  have hgap : positiveWeight (n + 1) / 3 -
      2 * ((n : ℝ) + 1) *
        (DigammaAsymptotic.inversePowerDifference ((n : ℝ) + 1) 2 / 12) =
      1 / (6 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2) := by
    unfold positiveWeight DigammaAsymptotic.inversePowerDifference
    push_cast
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [h1, h2]
    <;> ring
  have hpos : 0 < 1 / (6 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2) := by positivity
  linarith

theorem centeredEnergy_lt_third_weight (n : ℕ) :
    centeredEnergy n < positiveWeight (n + 1) / 3 :=
  (centeredEnergy_le_raw n).trans_lt (rawResidueCellEnergy_lt_third_weight n)


end RiemannResearch.RH.StepCorrectionNorm
