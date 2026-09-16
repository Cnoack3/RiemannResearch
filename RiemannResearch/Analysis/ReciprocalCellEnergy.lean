import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Reciprocal-square interval energy

Source: user-provided V_Zeta_Vector_Spaces_Research_2026-09-16.md,
continuation Section 12.1. The actual integral with density x^-2 splits into
the squared weighted-mean discrepancy plus a nonnegative geometric remainder.
Its two-sided cubic-gap bounds are proved by exact polynomial integration and
density comparison. The RH consumer is RH/PrimePowerCriticalEnergy.
-/

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.Analysis.ReciprocalCellEnergy

def intervalWeight (a b : ℝ) : ℝ := 1 / a - 1 / b
def intervalMean (a b : ℝ) : ℝ := Real.log (b / a) / intervalWeight a b
def intervalRemainder (a b : ℝ) : ℝ :=
  (b - a) - Real.log (b / a) ^ 2 / intervalWeight a b

theorem intervalWeight_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < intervalWeight a b := by
  have hb : 0 < b := lt_trans ha hab
  have he : intervalWeight a b = (b - a) / (a * b) := by
    unfold intervalWeight
    field_simp [ne_of_gt ha, ne_of_gt hb]
  rw [he]
  exact div_pos (sub_pos.mpr hab) (mul_pos ha hb)

theorem integral_residual_square {a b : ℝ} (ha : 0 < a) (hab : a < b) (c : ℝ) :
    (∫ x in a..b, (c - x) ^ 2 / x ^ 2) =
      intervalWeight a b * c ^ 2 - 2 * Real.log (b / a) * c + (b - a) := by
  have hb : 0 < b := lt_trans ha hab
  have hxne : ∀ x ∈ uIcc a b, x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hcont : ContinuousOn (fun x : ℝ => (c - x) ^ 2 / x ^ 2) (uIcc a b) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (hxne x hx)
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt
        (fun y : ℝ => -(c ^ 2) * y⁻¹ - (2 * c) * Real.log y + y)
        ((c - x) ^ 2 / x ^ 2) x := by
    intro x hx
    have hn := hxne x hx
    convert (((hasDerivAt_inv hn).const_mul (-(c ^ 2))).sub
      ((Real.hasDerivAt_log hn).const_mul (2 * c))).add (hasDerivAt_id x) using 1
    all_goals first | rfl | (field_simp [hn]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)]
  unfold intervalWeight
  simp only [one_div]
  ring

theorem integral_residual_square_split {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (c : ℝ) :
    (∫ x in a..b, (c - x) ^ 2 / x ^ 2) =
      intervalWeight a b * (c - intervalMean a b) ^ 2 + intervalRemainder a b := by
  rw [integral_residual_square ha hab]
  have hw : intervalWeight a b ≠ 0 := ne_of_gt (intervalWeight_pos ha hab)
  unfold intervalMean intervalRemainder
  field_simp [hw]
  ring

theorem integral_mean_residual_square {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ x in a..b, (intervalMean a b - x) ^ 2 / x ^ 2) =
      intervalRemainder a b := by
  simpa using integral_residual_square_split ha hab (intervalMean a b)

theorem intervalRemainder_nonneg {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 ≤ intervalRemainder a b := by
  rw [← integral_mean_residual_square ha hab]
  exact intervalIntegral.integral_nonneg hab.le
    (fun x hx => div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem intervalMean_minimizes {a b : ℝ} (ha : 0 < a) (hab : a < b) (c : ℝ) :
    intervalRemainder a b ≤ (∫ x in a..b, (c - x) ^ 2 / x ^ 2) := by
  rw [integral_residual_square_split ha hab]
  exact le_add_of_nonneg_left
    (mul_nonneg (intervalWeight_pos ha hab).le (sq_nonneg _))

theorem integral_interval_correction_cost {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (c : ℝ) :
    (∫ x in a..b, (intervalMean a b - c) ^ 2 / x ^ 2) =
      intervalWeight a b * (c - intervalMean a b) ^ 2 := by
  have hz : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab.le]
    intro hx
    exact (not_le_of_gt ha) hx.1
  have hp := integral_zpow (a := a) (b := b) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hz⟩)
  have hf : (fun x : ℝ => (intervalMean a b - c) ^ 2 / x ^ 2) =
      fun x : ℝ => (intervalMean a b - c) ^ 2 * x ^ (-2 : ℤ) := by
    funext x
    simp [div_eq_mul_inv]
  rw [hf, intervalIntegral.integral_const_mul, hp]
  unfold intervalWeight
  norm_num
  ring

/-- Exact unweighted quadratic moment, with its minimizing midpoint explicit. -/
theorem integral_unweighted_residual_square (a b c : ℝ) :
    (∫ x in a..b, (c - x) ^ 2) =
      (b - a) * (c - (a + b) / 2) ^ 2 + (b - a) ^ 3 / 12 := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => c ^ 2 * y - c * y ^ 2 + y ^ 3 / 3)
        ((c - x) ^ 2) x := by
    convert (((hasDerivAt_id x).const_mul (c ^ 2)).sub
      (((hasDerivAt_id x).pow 2).const_mul c)).add
        (((hasDerivAt_id x).pow 3).div_const 3) using 1
    all_goals first | rfl | (dsimp; ring)
  have hi : IntervalIntegrable (fun x : ℝ => (c - x) ^ 2) volume a b :=
    (by fun_prop : Continuous (fun x : ℝ => (c - x) ^ 2)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv x) hi]
  ring

theorem integral_unweighted_residual_square_div (a b c d : ℝ) :
    (∫ x in a..b, (c - x) ^ 2 / d) =
      ((b - a) * (c - (a + b) / 2) ^ 2 + (b - a) ^ 3 / 12) / d := by
  rw [intervalIntegral.integral_div, integral_unweighted_residual_square]

theorem intervalIntegrable_weighted_residual_square {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (c : ℝ) :
    IntervalIntegrable (fun x : ℝ => (c - x) ^ 2 / x ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  rw [uIcc_of_le hab.le] at hx
  exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le ha hx.1))

/-- The midpoint test gives the upper cubic bound, without a Taylor remainder. -/
theorem intervalRemainder_le_cubic {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    intervalRemainder a b ≤ (b - a) ^ 3 / (12 * a ^ 2) := by
  have hc : Continuous (fun x : ℝ => ((a + b) / 2 - x) ^ 2 / a ^ 2) := by
    fun_prop
  have hcompare :
      (∫ x in a..b, ((a + b) / 2 - x) ^ 2 / x ^ 2) ≤
        ∫ x in a..b, ((a + b) / 2 - x) ^ 2 / a ^ 2 := by
    apply intervalIntegral.integral_mono_on hab.le
      (intervalIntegrable_weighted_residual_square ha hab _) (hc.intervalIntegrable a b)
    intro x hx
    have hx0 : 0 ≤ x := le_trans ha.le hx.1
    apply div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos ha 2)
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (add_nonneg hx0 ha.le)]
  calc
    intervalRemainder a b ≤
        ∫ x in a..b, ((a + b) / 2 - x) ^ 2 / x ^ 2 :=
      intervalMean_minimizes ha hab ((a + b) / 2)
    _ ≤ ∫ x in a..b, ((a + b) / 2 - x) ^ 2 / a ^ 2 := hcompare
    _ = (b - a) ^ 3 / (12 * a ^ 2) := by
      rw [integral_unweighted_residual_square_div]
      simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, div_div]

/-- Comparing densities with b^-2 gives the matching lower cubic bound. -/
theorem cubic_le_intervalRemainder {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b - a) ^ 3 / (12 * b ^ 2) ≤ intervalRemainder a b := by
  have hb : 0 < b := lt_trans ha hab
  have hc : Continuous (fun x : ℝ => (intervalMean a b - x) ^ 2 / b ^ 2) := by
    fun_prop
  have hcompare :
      (∫ x in a..b, (intervalMean a b - x) ^ 2 / b ^ 2) ≤
        ∫ x in a..b, (intervalMean a b - x) ^ 2 / x ^ 2 := by
    apply intervalIntegral.integral_mono_on hab.le (hc.intervalIntegrable a b)
      (intervalIntegrable_weighted_residual_square ha hab _)
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    apply div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hxpos 2)
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hb.le hxpos.le)]
  have hnonneg : 0 ≤ (b - a) * (intervalMean a b - (a + b) / 2) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hab.le) (sq_nonneg _)
  have hbaseline : (b - a) ^ 3 / 12 ≤
      (b - a) * (intervalMean a b - (a + b) / 2) ^ 2 + (b - a) ^ 3 / 12 :=
    le_add_of_nonneg_left hnonneg
  calc
    (b - a) ^ 3 / (12 * b ^ 2) = ((b - a) ^ 3 / 12) / b ^ 2 :=
      (div_div _ _ _).symm
    _ ≤ ((b - a) * (intervalMean a b - (a + b) / 2) ^ 2 +
        (b - a) ^ 3 / 12) / b ^ 2 :=
      div_le_div_of_nonneg_right hbaseline (sq_nonneg b)
    _ = ∫ x in a..b, (intervalMean a b - x) ^ 2 / b ^ 2 :=
      (integral_unweighted_residual_square_div _ _ _ _).symm
    _ ≤ ∫ x in a..b, (intervalMean a b - x) ^ 2 / x ^ 2 := hcompare
    _ = intervalRemainder a b := integral_mean_residual_square ha hab

theorem intervalRemainder_cubic_bounds {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b - a) ^ 3 / (12 * b ^ 2) ≤ intervalRemainder a b ∧
      intervalRemainder a b ≤ (b - a) ^ 3 / (12 * a ^ 2) :=
  ⟨cubic_le_intervalRemainder ha hab, intervalRemainder_le_cubic ha hab⟩

/-! Elementary interval bounds used by the unconditional arithmetic estimates. -/

theorem interval_excess_le_linear_of_level_bound {a b c K : ℝ}
    (ha : 0 < a) (hab : a < b) (hK : 1 ≤ K) (hc0 : 0 ≤ c) (hc : c ≤ K * a) :
    intervalWeight a b * (c - intervalMean a b) ^ 2 ≤ K ^ 2 * (b - a) := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hi : (∫ x in a..b, (c - x) ^ 2 / x ^ 2) ≤ K ^ 2 * (b - a) := by
    calc
      _ ≤ ∫ x in a..b, K ^ 2 := by
        apply intervalIntegral.integral_mono_on hab.le
          (intervalIntegrable_weighted_residual_square ha hab c) intervalIntegrable_const
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
        have hcx : c ≤ K * x := hc.trans (mul_le_mul_of_nonneg_left hx.1 hK0)
        have hxK : x ≤ K * x := by nlinarith
        have hs : (c - x) ^ 2 ≤ (K * x) ^ 2 :=
          sq_le_sq' (by linarith) (by linarith)
        apply (div_le_iff₀ (sq_pos_of_pos hx0)).mpr
        nlinarith
      _ = _ := by simp [mul_comm]
  rw [integral_residual_square_split ha hab c] at hi
  linarith [intervalRemainder_nonneg ha hab]


theorem intervalMean_nonneg {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 ≤ intervalMean a b := by
  apply div_nonneg _ (intervalWeight_pos ha hab).le
  exact Real.log_nonneg ((le_div_iff₀ ha).mpr (by linarith))

theorem intervalMean_le_right {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    intervalMean a b ≤ b := by
  have hb : 0 < b := ha.trans hab
  apply (div_le_iff₀ (intervalWeight_pos ha hab)).mpr
  have he : b * intervalWeight a b = b / a - 1 := by
    unfold intervalWeight
    field_simp
  rw [he]
  exact Real.log_le_sub_one_of_pos (div_pos hb ha)


end RiemannResearch.Analysis.ReciprocalCellEnergy
