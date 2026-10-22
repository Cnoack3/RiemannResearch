import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Vanishing defect from a critical moving double-log margin

Source: user-requested backwards RH verification, 13 October 2026.
These conditional deductions are independently formalized, without a novelty claim.
No missing arithmetic bound is asserted.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.FiniteSpectralBudget

/-- An elementary replacement for exponential/rpow asymptotics. -/
theorem log_sub_lower_of_twice_lt {a K : ℝ} (hK : 0 ≤ K) (ha : 2 * K < a) :
    Real.log a - 2 * K / a ≤ Real.log (a - K) := by
  have ha0 : 0 < a := by linarith
  have hak : 0 < a - K := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos ha0 hak)
  rw [Real.log_div ha0.ne' hak.ne'] at hl
  have hid : a / (a - K) - 1 = K / (a - K) := by
    field_simp [hak.ne']
    <;> ring
  rw [hid] at hl
  have hratio : K / (a - K) ≤ 2 * K / a := by
    apply (div_le_div_iff₀ hak ha0).mpr
    nlinarith [mul_nonneg hK (le_of_lt (sub_pos.mpr ha))]
  linarith

/-- Clear only positive denominators in the critical feedback inequality. -/
theorem critical_feedback_algebra {a T J E K : ℝ}
    (ha : 0 < a) (hD : 0 < Real.log a)
    (hlower : T * (Real.log a - 2 * K / a) ≤ J)
    (hupper : J ≤ (Real.log a - Real.log a / a) * T + Real.log a * E) :
    (1 - 2 * K / Real.log a) * T ≤ a * E := by
  have hh := mul_le_mul_of_nonneg_left (hlower.trans hupper) ha.le
  have hleft : a * (T * (Real.log a - 2 * K / a)) =
      a * T * Real.log a - 2 * K * T := by
    field_simp [ha.ne']
    <;> ring
  have hright : a * ((Real.log a - Real.log a / a) * T + Real.log a * E) =
      a * Real.log a * T - Real.log a * T + a * Real.log a * E := by
    field_simp [ha.ne']
    <;> ring
  rw [hleft, hright] at hh
  apply (mul_le_mul_iff_right₀ hD).mp
  have hclean : Real.log a * ((1 - 2 * K / Real.log a) * T) =
      Real.log a * T - 2 * K * T := by
    field_simp [hD.ne']
    <;> ring
  rw [hclean]
  nlinarith only [hh]

/-- Critical margin 1/a with additive error o(1/a) forces the limiting correction to zero.

The lower bound is the finite Jensen estimate after using S ≤ sigma and
setting a = 1 + log(1/sigma). Its positivity premise is explicit: for extremely
small T, a + log T need not be positive.
-/
theorem defect_eq_zero_of_critical_doubleLog_feedback
    (a T J E : ℕ → ℝ) (q : ℝ)
    (hT : Tendsto T atTop (𝓝 q))
    (ha : Tendsto a atTop atTop)
    (hE : Tendsto (fun n => a n * E n) atTop (𝓝 0))
    (hTnonneg : ∀ n, 0 ≤ T n)
    (hjensen : ∀ᶠ n in atTop, 0 < T n → 0 < a n + Real.log (T n) →
      T n * Real.log (a n + Real.log (T n)) ≤ J n)
    (hbudget : ∀ᶠ n in atTop,
      J n ≤ (Real.log (a n) - Real.log (a n) / a n) * T n +
        Real.log (a n) * E n) : q = 0 := by
  have hq0 : 0 ≤ q := le_of_tendsto_of_tendsto tendsto_const_nhds hT
    (Filter.Eventually.of_forall hTnonneg)
  by_contra hq
  have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
  let eps : ℝ := min (q / 2) 1
  have heps : 0 < eps := by dsimp [eps]; exact lt_min (by linarith) zero_lt_one
  have heps1 : eps ≤ 1 := min_le_right _ _
  have hepsq : eps < q := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let K : ℝ := -Real.log eps
  have hK : 0 ≤ K := neg_nonneg.mpr (Real.log_nonpos heps.le heps1)
  have hTe : ∀ᶠ n in atTop, eps ≤ T n :=
    (hT.eventually (eventually_gt_nhds hepsq)).mono fun _ hn => hn.le
  have haBig : ∀ᶠ n in atTop, max (2 * K) 1 < a n :=
    ha.eventually (eventually_gt_atTop _)
  have hD : Tendsto (fun n => Real.log (a n)) atTop atTop :=
    Real.tendsto_log_atTop.comp ha
  have hfinal : ∀ᶠ n in atTop,
      (1 - 2 * K / Real.log (a n)) * T n ≤ a n * E n := by
    filter_upwards [hTe, haBig, hjensen, hbudget] with n hnT hna hnJ hnB
    have haK : 2 * K < a n := lt_of_le_of_lt (le_max_left _ _) hna
    have ha1 : 1 < a n := lt_of_le_of_lt (le_max_right _ _) hna
    have ha0 : 0 < a n := by linarith
    have hak : 0 < a n - K := by linarith
    have hTpos : 0 < T n := heps.trans_le hnT
    have hlogT : -K ≤ Real.log (T n) := by
      have hh := Real.log_le_log heps hnT
      simpa only [K, neg_neg] using hh
    have hinside : a n - K ≤ a n + Real.log (T n) := by linarith
    have hinsidepos : 0 < a n + Real.log (T n) := hak.trans_le hinside
    have hloglower : Real.log (a n) - 2 * K / a n ≤
        Real.log (a n + Real.log (T n)) :=
      (log_sub_lower_of_twice_lt hK haK).trans (Real.log_le_log hak hinside)
    have hjlow : T n * (Real.log (a n) - 2 * K / a n) ≤ J n :=
      (mul_le_mul_of_nonneg_left hloglower (hTnonneg n)).trans
        (hnJ hTpos hinsidepos)
    exact critical_feedback_algebra ha0 (Real.log_pos ha1) hjlow hnB
  have hleft : Tendsto (fun n => (1 - 2 * K / Real.log (a n)) * T n)
      atTop (𝓝 q) := by
    simpa only [sub_zero, one_mul] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * K) atTop (𝓝 (2 * K))).div_atTop hD)).mul hT
  have hqle : q ≤ 0 := le_of_tendsto_of_tendsto hleft hE hfinal
  exact (not_le_of_gt hqpos) hqle

end RiemannResearch.Analysis.FiniteSpectralBudget
