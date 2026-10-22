import RiemannResearch.Analysis.DilogarithmSeries
import RiemannResearch.RH.TrivialZeroLogIntegral
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The integrated trivial-zero power series

Source: user-provided prime-phases manuscript; the dilogarithm series is
NIST DLMF 25.12.1. This evaluates the series as its exact logarithmic
integral and gives a positive explicit error bound. Its identification
with the arithmetic integrated explicit formula is a separate analytic obligation.
-/

noncomputable section
open scoped BigOperators Interval
namespace RiemannResearch.RH.IntegratedTrivialZeroTerm
open RiemannResearch.Analysis

def term (x : ℝ) (n : ℕ) : ℝ :=
  (DilogarithmSeries.term (4/x^2) n - DilogarithmSeries.term (1/x^2) n) / 4
def correction (x : ℝ) : ℝ := ∑' n : ℕ, term x n

private theorem ratios {x : ℝ} (hx : 2 < x) :
    0 ≤ 1/x^2 ∧ 1/x^2 ≤ 4/x^2 ∧ 0 ≤ 4/x^2 ∧ 4/x^2 < 1 := by
  have hx2 : 4 < x^2 := by nlinarith
  have hp : 0 < x^2 := lt_trans (by norm_num) hx2
  refine ⟨by positivity, ?_, by positivity, (div_lt_one hp).mpr hx2⟩
  exact div_le_div_of_nonneg_right (by norm_num) hp.le

theorem term_nonneg {x : ℝ} (hx : 2 < x) (n : ℕ) : 0 ≤ term x n := by
  obtain ⟨hs, hsr, hr, hr1⟩ := ratios hx
  apply div_nonneg _ (by norm_num)
  apply sub_nonneg.mpr
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hs hsr _)
    (sq_nonneg _)

theorem term_le_geometric {x : ℝ} (hx : 2 < x) (n : ℕ) :
    term x n ≤ (4/x^2)^(n+1)/4 := by
  obtain ⟨hs, hsr, hr, hr1⟩ := ratios hx
  unfold term
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have h := DilogarithmSeries.term_le_pow hr n
  have h0 := DilogarithmSeries.term_nonneg hs n
  linarith

theorem summable_term {x : ℝ} (hx : 2 < x) : Summable (term x) := by
  obtain ⟨hs, hsr, hr, hr1⟩ := ratios hx
  exact ((DilogarithmSeries.summable_term hr hr1).sub
    (DilogarithmSeries.summable_term hs (lt_of_le_of_lt hsr hr1))).div_const 4

theorem correction_eq_dilogarithm {x : ℝ} (hx : 2 < x) :
    correction x = (DilogarithmSeries.value (4/x^2) - DilogarithmSeries.value (1/x^2))/4 := by
  obtain ⟨hs, hsr, hr, hr1⟩ := ratios hx
  unfold correction term DilogarithmSeries.value
  rw [tsum_div_const, (DilogarithmSeries.summable_term hr hr1).tsum_sub
    (DilogarithmSeries.summable_term hs (lt_of_le_of_lt hsr hr1))]

theorem correction_eq_log_integral {x : ℝ} (hx : 2 < x) :
    correction x =
      ∫ t in (x / 2)..x, -Real.log (1 - (t⁻¹) ^ 2) / (2 * t) := by
  calc
    correction x = (DilogarithmSeries.value (4 / x ^ 2) -
        DilogarithmSeries.value (1 / x ^ 2)) / 4 := correction_eq_dilogarithm hx
    _ = (1 / 4 : ℝ) * (DilogarithmSeries.value (4 / x ^ 2) -
        DilogarithmSeries.value (1 / x ^ 2)) := by ring
    _ = ∫ t in (x / 2)..x, -Real.log (1 - (t⁻¹) ^ 2) / (2 * t) :=
      TrivialZeroLogIntegral.dyadic_dilog_eq_log_integral hx

theorem correction_nonneg {x : ℝ} (hx : 2 < x) : 0 ≤ correction x :=
  tsum_nonneg (term_nonneg hx)

theorem correction_le {x : ℝ} (hx : 2 < x) :
    correction x ≤ 1/(x^2-4) := by
  obtain ⟨hs, hsr, hr, hr1⟩ := ratios hx
  have hg : Summable (fun n : ℕ => (4/x^2)^(n+1)/4) := by
    have h : Summable (fun n : ℕ => (4/x^2)^(n+1)) := by
      have hraw : Summable (fun n : ℕ => (4/x^2) * (4/x^2)^n) :=
        (hasSum_geometric_of_lt_one hr hr1).summable.mul_left (4/x^2)
      exact hraw.congr (fun n => (pow_succ' (4/x^2) n).symm)
    exact h.div_const 4
  calc
    correction x ≤ ∑' n : ℕ, (4/x^2)^(n+1)/4 :=
      (summable_term hx).tsum_le_tsum (term_le_geometric hx) hg
    _ = (4/x^2)/(1-4/x^2)/4 := by
      rw [tsum_div_const, DilogarithmSeries.shifted_geometric hr hr1]
    _ = 1/(x^2-4) := by
      have hx2 : 4 < x^2 := by nlinarith
      have hq : (0 : ℝ) < x^2 := by linarith
      field_simp [hq.ne', ne_of_gt (sub_pos.mpr hx2)]
      <;> ring

theorem first_term_le_correction {x : ℝ} (hx : 2 < x) :
    3/(4*x^2) ≤ correction x := by
  have h := (summable_term hx).le_tsum 0 (fun n _ => term_nonneg hx n)
  have he : term x 0 = 3/(4*x^2) := by
    unfold term DilogarithmSeries.term
    norm_num
    ring
  rw [he] at h
  exact h

theorem correction_pos {x : ℝ} (hx : 2 < x) : 0 < correction x :=
  lt_of_lt_of_le (by positivity) (first_term_le_correction hx)

theorem correction_le_two_div_sq {x : ℝ} (hx : 3 ≤ x) :
    correction x ≤ 2/x^2 := by
  have hx2 : 9 ≤ x^2 := by nlinarith
  have hp : 0 < x^2-4 := by linarith
  have hq : 0 < x^2 := by linarith
  apply le_trans (correction_le (by linarith))
  apply (div_le_div_iff₀ hp hq).mpr
  nlinarith

theorem correction_isBigO :
    Asymptotics.IsBigO Filter.atTop correction (fun x : ℝ => x^(-2 : ℤ)) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (correction_nonneg (by linarith))]
  simpa [zpow_neg, zpow_ofNat, div_eq_mul_inv, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ x)] using correction_le_two_div_sq hx

end RiemannResearch.RH.IntegratedTrivialZeroTerm
